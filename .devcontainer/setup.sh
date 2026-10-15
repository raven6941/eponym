#!/bin/bash
# Eponym devcontainer setup: install Nim, build LSP and VS Code extension.
set -e

echo "Installing Nim via choosenim..."
curl -sSf https://nim-lang.org/choosenim/init.sh | sh -s -- -y
export PATH="$HOME/.nimble/bin:$PATH"

echo "Building Eponym LSP..."
cd "${PWD}"
nim c --path:src --path:src/eponym src/eponym/lsp.nim

echo "Building VS Code extension..."
cd editors/vscode
npm install
npm run build

echo "Eponym devcontainer ready."
