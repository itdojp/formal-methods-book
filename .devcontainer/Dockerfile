FROM mcr.microsoft.com/devcontainers/dotnet:8.0-jammy

RUN apt-get update \
  && apt-get install -y --no-install-recommends \
    openjdk-17-jre-headless \
    curl \
    unzip \
    ca-certificates \
  && rm -rf /var/lib/apt/lists/*
