#!/bin/bash
# Compiles the Cairo bootloader found in the cairo-lang submodule.
# The compiled bootloader is versioned to make compilation easier. This script is currently only used
# to recompile the bootloader when changing the version of cairo-lang.

SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
CAIRO_VERSION="0.13.0"

CAIRO_LANG_DIR=$(readlink -f "${SCRIPT_DIR}/../dependencies/cairo-lang")

if ! command -v cairo-compile >/dev/null; then
    echo "please start cairo ($CAIRO_VERSION) dev environment"
    exit 1
fi

echo -e "\ninitializing cairo-lang ($CAIRO_VERSION)...\n"
git submodule update --init

FETCHED_CAIRO_VER="$(cat "${CAIRO_LANG_DIR}/src/starkware/cairo/lang/VERSION")"

if [ "$CAIRO_VERSION" != "$FETCHED_CAIRO_VER" ]; then
    echo "incorrect cairo ver($FETCHED_CAIRO_VER) expecting $CAIRO_VERSION"
    exit 1
fi

OUTPUT_DIR="$(readlink -f "${SCRIPT_DIR}/../resources")"
mkdir -p "${OUTPUT_DIR}"
COMPILED_BOOTLOADER="${OUTPUT_DIR}/bootloader-${CAIRO_VERSION}.json"

cairo-compile \
  "${CAIRO_LANG_DIR}/src/starkware/cairo/bootloaders/bootloader/bootloader.cairo" \
  --output "${COMPILED_BOOTLOADER}" \
  --cairo_path "${CAIRO_LANG_DIR}"/src \
  --proof_mode

echo "Compiled the bootloader to '${COMPILED_BOOTLOADER}'."