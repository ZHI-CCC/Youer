package net.neoforged.neodev.installer;

import net.neoforged.neodev.utils.MavenIdentifier;
import org.gradle.api.logging.Logger;
import org.gradle.api.logging.Logging;

import java.io.File;
import java.io.IOException;
import java.io.StringReader;
import java.io.UncheckedIOException;
import java.net.URI;
import java.net.http.HttpClient;
import java.net.http.HttpRequest;
import java.net.http.HttpResponse;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.security.DigestInputStream;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.time.Duration;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HexFormat;
import java.util.List;
import java.util.Locale;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.CompletionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.function.Function;
import javax.xml.XMLConstants;
import javax.xml.parsers.DocumentBuilderFactory;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.InputSource;

/**
 * For each file in a collection, finds the repository that the file came from.
 */
class LibraryCollector implements AutoCloseable {
    public static List<Library> resolveLibraries(List<URI> repositoryUrls, Collection<IdentifiedFile> libraries) throws IOException {
        try (var collector = new LibraryCollector(repositoryUrls)) {
            for (var library : libraries) {
                collector.addLibrary(library.getFile().getAsFile().get(), library.getIdentifier().get());
            }

            var result = collector.libraries.stream().map(future -> {
                try {
                    return future.get();
                } catch (Exception e) {
                    throw new RuntimeException(e);
                }
            }).toList();
            LOGGER.info("Collected {} libraries", result.size());
            return result;
        }
    }

    private static final Logger LOGGER = Logging.getLogger(LibraryCollector.class);
    private static final String ALIYUN_MAVEN_HOST = "maven.aliyun.com";
    private static final int MAX_CONCURRENT_REQUESTS = 8;
    private static final int MAX_HEAD_RETRIES = 3;
    private static final Duration REQUEST_TIMEOUT = Duration.ofSeconds(30);

    /**
     * Hosts from which we allow the installer to download.
     * These are the canonical hosts explicitly declared in settings.gradle. Keeping this
     * list explicit prevents a local Maven repository from leaking into a release profile.
     */
    private static final List<String> HOST_WHITELIST = List.of(
            "minecraft.net",
            "neoforged.net",
            "mojang.com",
            "mohistmc.com",
            "github.io",
            "spigotmc.org",
            "papermc.io",
            "jitpack.io",
            "createmod.net",
            "ryanhcode.dev",
            "minecraftforge.net",
            "modrinth.com",
            ALIYUN_MAVEN_HOST
    );

    private static final URI MOJANG_MAVEN = URI.create("https://libraries.minecraft.net");
    private static final URI NEOFORGED_MAVEN = URI.create("https://maven.neoforged.net/releases");
    private static final URI MOHISTMC_MAVEN = URI.create("https://maven.mohistmc.com");
    private static final URI JITPACK_MAVEN = URI.create("https://jitpack.io");

    private record ArtifactLocation(URI uri, String path) {}

    private final List<URI> repositoryUrls;

    private final List<Future<Library>> libraries = new ArrayList<>();
    private final ExecutorService requestExecutor = Executors.newFixedThreadPool(MAX_CONCURRENT_REQUESTS);

    private final HttpClient httpClient = HttpClient.newBuilder()
            .followRedirects(HttpClient.Redirect.NORMAL)
            .version(HttpClient.Version.HTTP_1_1)
            .build();

    private LibraryCollector(List<URI> repoUrl) {
        this.repositoryUrls = new ArrayList<>(repoUrl);

        // Only remote repositories make sense (no maven local)
        repositoryUrls.removeIf(it -> {
            var lowercaseScheme = it.getScheme().toLowerCase(Locale.ROOT);
            return !lowercaseScheme.equals("https") && !lowercaseScheme.equals("http");
        });
        // Allow only URLs from whitelisted hosts
        repositoryUrls.removeIf(uri -> {
            var lowercaseHost = uri.getHost().toLowerCase(Locale.ROOT);
            return HOST_WHITELIST.stream().noneMatch(it -> lowercaseHost.equals(it) || lowercaseHost.endsWith("." + it));
        });
        var aliyunMaven = repositoryUrls.stream()
                .filter(uri -> uri.getHost().equalsIgnoreCase(ALIYUN_MAVEN_HOST))
                .findFirst()
                .orElse(null);
        // Always try Mohist and Mojang first, then the configured public mirror before NeoForge.
        repositoryUrls.removeIf(it -> it.getHost().equals(MOJANG_MAVEN.getHost()));
        // ModDev also contributes the mojang-meta endpoint. It is not a Maven
        // artifact repository, so probing it only adds failing TLS requests.
        repositoryUrls.removeIf(it -> it.getHost().equals(NEOFORGED_MAVEN.getHost()));
        repositoryUrls.removeIf(it -> it.getHost().equals(MOHISTMC_MAVEN.getHost()) && it.getPath().startsWith(MOHISTMC_MAVEN.getPath()));
        repositoryUrls.removeIf(it -> it.getHost().equalsIgnoreCase(ALIYUN_MAVEN_HOST));
        repositoryUrls.addFirst(NEOFORGED_MAVEN);
        if (aliyunMaven != null) {
            repositoryUrls.addFirst(aliyunMaven);
        }
        repositoryUrls.addFirst(MOJANG_MAVEN);
        repositoryUrls.addFirst(MOHISTMC_MAVEN);

        LOGGER.info("Collecting libraries from:");
        for (var repo : repositoryUrls) {
            LOGGER.info(" - {}", repo);
        }
    }

    private void addLibrary(File file, MavenIdentifier identifier) throws IOException {
        final String name = identifier.artifactNotation();
        final String path = identifier.repositoryPath();

        var sha1 = sha1Hash(file.toPath());
        var fileSize = Files.size(file.toPath());

        // Aliyun mirrors the public subset of NeoForge's Maven repository, but not all
        // FML/NeoForge runtime artifacts. Avoid probing the official endpoint here: its
        // availability is irrelevant to profile generation and some local proxies reject
        // the JDK HTTP client's TLS handshake. The launcher still receives the canonical
        // official URL when the mirror does not contain the artifact.
        var candidateRepositoryUrls = isNeoForgeRuntimeLibrary(identifier)
                ? repositoryUrls.stream().filter(LibraryCollector::isAliyunMaven).toList()
                : repositoryUrls;

        // Try each configured repository in-order to find the file
        CompletableFuture<Library> libraryFuture = null;
        for (var repositoryUrl : candidateRepositoryUrls) {
            Function<String, CompletableFuture<Library>> makeRequest = (String previousError) -> {
                return artifactLocationFor(repositoryUrl, identifier)
                        .thenCompose(location -> {
                            return probeArtifact(location.uri()).thenApply(response -> {
                                if (!isSuccessfulArtifactResponse(response.statusCode())) {
                                    LOGGER.info("  Got {} for {}", response.statusCode(), location.uri());
                                    String message = "Could not find %s: %d".formatted(location.uri(), response.statusCode());
                                    // Prepend error message from previous repo if they all fail
                                    if (previousError != null) {
                                        message = previousError + "\n" + message;
                                    }
                                    throw new RuntimeException(message);
                                }
                                LOGGER.info("  Found {} -> {}", name, location.uri());
                                return createLibrary(name, sha1, fileSize, location.uri(), location.path());
                            });
                        });
            };

            if (libraryFuture == null) {
                libraryFuture = makeRequest.apply(null);
            } else {
                libraryFuture = libraryFuture.exceptionallyCompose(error -> {
                    if (error instanceof CompletionException e) {
                        return makeRequest.apply(e.getCause().getMessage());
                    }
                    return makeRequest.apply(error.getMessage());
                });
            }
        }

        if (isNeoForgeRuntimeLibrary(identifier)) {
            var officialArtifactUri = joinUris(NEOFORGED_MAVEN, path);
            if (libraryFuture == null) {
                LOGGER.info("  Using canonical NeoForge Maven URL for {}", name);
                libraryFuture = CompletableFuture.completedFuture(createLibrary(name, sha1, fileSize, officialArtifactUri, path));
            } else {
                libraryFuture = libraryFuture.exceptionallyCompose(error -> {
                    LOGGER.info("  {} is unavailable from Aliyun; using canonical NeoForge Maven URL", name);
                    return CompletableFuture.completedFuture(createLibrary(name, sha1, fileSize, officialArtifactUri, path));
                });
            }
        }

        libraries.add(libraryFuture);
    }

    private CompletableFuture<ArtifactLocation> artifactLocationFor(URI repositoryUrl, MavenIdentifier identifier) {
        if (!identifier.version().endsWith("-SNAPSHOT")) {
            var path = identifier.repositoryPath();
            return CompletableFuture.completedFuture(new ArtifactLocation(joinUris(repositoryUrl, path), path));
        }

        var metadataPath = identifier.group().replace('.', '/') + "/" + identifier.artifact() + "/" + identifier.version() + "/maven-metadata.xml";
        var metadataUri = joinUris(repositoryUrl, metadataPath);
        var request = HttpRequest.newBuilder(metadataUri)
                .timeout(REQUEST_TIMEOUT)
                .GET()
                .build();
        return send(request, HttpResponse.BodyHandlers.ofString(StandardCharsets.UTF_8))
                .thenApply(response -> {
                    if (response.statusCode() != 200) {
                        throw new RuntimeException("Could not find %s: %d".formatted(metadataUri, response.statusCode()));
                    }

                    var resolvedVersion = resolveSnapshotVersion(response.body(), identifier);
                    var filename = identifier.artifact() + "-" + resolvedVersion
                            + (identifier.classifier().isEmpty() ? "" : "-" + identifier.classifier())
                            + "." + identifier.extension();
                    var path = identifier.group().replace('.', '/') + "/" + identifier.artifact() + "/" + identifier.version() + "/" + filename;
                    return new ArtifactLocation(joinUris(repositoryUrl, path), path);
                });
    }

    private static String resolveSnapshotVersion(String metadata, MavenIdentifier identifier) {
        try {
            var factory = DocumentBuilderFactory.newInstance();
            factory.setFeature(XMLConstants.FEATURE_SECURE_PROCESSING, true);
            factory.setFeature("http://apache.org/xml/features/disallow-doctype-decl", true);
            factory.setFeature("http://xml.org/sax/features/external-general-entities", false);
            factory.setFeature("http://xml.org/sax/features/external-parameter-entities", false);
            factory.setAttribute(XMLConstants.ACCESS_EXTERNAL_DTD, "");
            factory.setAttribute(XMLConstants.ACCESS_EXTERNAL_SCHEMA, "");
            factory.setXIncludeAware(false);
            factory.setExpandEntityReferences(false);

            var document = factory.newDocumentBuilder().parse(new InputSource(new StringReader(metadata)));
            var versioning = childElement(document.getDocumentElement(), "versioning");
            var snapshotVersions = versioning == null ? null : childElement(versioning, "snapshotVersions");
            if (snapshotVersions != null) {
                var expectedClassifier = identifier.classifier();
                NodeList nodes = snapshotVersions.getChildNodes();
                for (int index = 0; index < nodes.getLength(); index++) {
                    Node node = nodes.item(index);
                    if (!(node instanceof Element snapshotVersion) || !snapshotVersion.getTagName().equals("snapshotVersion")) {
                        continue;
                    }
                    if (identifier.extension().equals(childText(snapshotVersion, "extension"))
                            && expectedClassifier.equals(childText(snapshotVersion, "classifier"))) {
                        var value = childText(snapshotVersion, "value");
                        if (!value.isEmpty()) {
                            return value;
                        }
                    }
                }
            }

            var snapshot = versioning == null ? null : childElement(versioning, "snapshot");
            var timestamp = snapshot == null ? "" : childText(snapshot, "timestamp");
            var buildNumber = snapshot == null ? "" : childText(snapshot, "buildNumber");
            if (!timestamp.isEmpty() && !buildNumber.isEmpty()) {
                var baseVersion = identifier.version().substring(0, identifier.version().length() - "-SNAPSHOT".length());
                return baseVersion + "-" + timestamp + "-" + buildNumber;
            }
        } catch (Exception exception) {
            throw new IllegalArgumentException("Could not parse Maven snapshot metadata for " + identifier.artifactNotation(), exception);
        }
        throw new IllegalArgumentException("Maven snapshot metadata has no matching artifact version for " + identifier.artifactNotation());
    }

    private static Element childElement(Element parent, String name) {
        NodeList nodes = parent.getChildNodes();
        for (int index = 0; index < nodes.getLength(); index++) {
            Node node = nodes.item(index);
            if (node instanceof Element child && child.getTagName().equals(name)) {
                return child;
            }
        }
        return null;
    }

    private static String childText(Element parent, String name) {
        var child = childElement(parent, name);
        return child == null ? "" : child.getTextContent().trim();
    }

    private static boolean isAliyunMaven(URI repositoryUrl) {
        return repositoryUrl.getHost().equalsIgnoreCase(ALIYUN_MAVEN_HOST);
    }

    private CompletableFuture<HttpResponse<Void>> probeArtifact(URI artifactUri) {
        var head = HttpRequest.newBuilder(artifactUri)
                .timeout(REQUEST_TIMEOUT)
                .method("HEAD", HttpRequest.BodyPublishers.noBody())
                .build();
        return sendHead(head).thenCompose(response -> {
            // JitPack currently answers HEAD for some otherwise downloadable
            // artifacts with 500. A one-byte GET verifies the URL without
            // downloading the full library during profile generation.
            if (isJitPack(artifactUri) && (response.statusCode() == 405 || response.statusCode() == 500)) {
                var get = HttpRequest.newBuilder(artifactUri)
                        .timeout(REQUEST_TIMEOUT)
                        .header("Range", "bytes=0-0")
                        .GET()
                        .build();
                return send(get, HttpResponse.BodyHandlers.discarding());
            }
            return CompletableFuture.completedFuture(response);
        });
    }

    private static boolean isSuccessfulArtifactResponse(int statusCode) {
        return statusCode == 200 || statusCode == 206;
    }

    private static boolean isJitPack(URI uri) {
        return uri.getHost().equalsIgnoreCase(JITPACK_MAVEN.getHost());
    }

    private static boolean isNeoForgeRuntimeLibrary(MavenIdentifier identifier) {
        var group = identifier.group();
        return group.equals("cpw.mods")
                || group.startsWith("cpw.mods.")
                || group.equals("net.neoforged")
                || group.startsWith("net.neoforged.")
                || group.equals("net.minecraftforge")
                || group.startsWith("net.minecraftforge.");
    }

    private static Library createLibrary(String name, String sha1, long fileSize, URI artifactUri, String path) {
        return new Library(
                name,
                new LibraryDownload(new LibraryArtifact(
                        sha1,
                        fileSize,
                        artifactUri.toString(),
                        path)));
    }

    private CompletableFuture<HttpResponse<Void>> sendHead(HttpRequest request) {
        return send(request, HttpResponse.BodyHandlers.discarding());
    }

    private <T> CompletableFuture<HttpResponse<T>> send(HttpRequest request, HttpResponse.BodyHandler<T> responseBodyHandler) {
        return CompletableFuture.supplyAsync(() -> {
            for (int attempt = 1; attempt <= MAX_HEAD_RETRIES; attempt++) {
                try {
                    return httpClient.send(request, responseBodyHandler);
                } catch (IOException exception) {
                    if (attempt == MAX_HEAD_RETRIES) {
                        throw new UncheckedIOException("Failed to query " + request.uri(), exception);
                    }
                    LOGGER.info("Retrying {} after I/O failure ({}/{})", request.uri(), attempt, MAX_HEAD_RETRIES);
                    try {
                        Thread.sleep(150L * attempt);
                    } catch (InterruptedException interrupted) {
                        Thread.currentThread().interrupt();
                        throw new CompletionException(interrupted);
                    }
                } catch (InterruptedException interrupted) {
                    Thread.currentThread().interrupt();
                    throw new CompletionException(interrupted);
                }
            }
            throw new AssertionError("Request retry loop completed without a result");
        }, requestExecutor);
    }

    @Override
    public void close() {
        requestExecutor.shutdownNow();
    }

    static String sha1Hash(Path path) throws IOException {
        MessageDigest digest;
        try {
            digest = MessageDigest.getInstance("SHA-1");
        } catch (NoSuchAlgorithmException e) {
            throw new RuntimeException(e);
        }

        try (var in = Files.newInputStream(path);
                var din = new DigestInputStream(in, digest)) {
            byte[] buffer = new byte[8192];
            while (din.read(buffer) != -1) {
            }
        }

        return HexFormat.of().formatHex(digest.digest());
    }

    private static URI joinUris(URI repositoryUrl, String path) {
        var baseUrl = repositoryUrl.toString();
        if (baseUrl.endsWith("/") && path.startsWith("/")) {
            while (path.startsWith("/")) {
                path = path.substring(1);
            }
            return URI.create(baseUrl + path);
        } else if (!baseUrl.endsWith("/") && !path.startsWith("/")) {
            return URI.create(baseUrl + "/" + path);
        } else {
            return URI.create(baseUrl + path);
        }
    }
}
