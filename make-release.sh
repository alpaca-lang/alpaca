#!/bin/bash

# If travis-ci is building a tag then use that as the version, otherwise mark
# this release with the hash from travis-ci:
VERSION=${TRAVIS_TAG:-${TRAVIS_COMMIT:-unversioned}}

# Where we're copying .beam files from:
ALPACA_BEAMS=_build/default/lib/alpaca/ebin

echo "Building release with version $VERSION"

REL_BASE=alpaca-$VERSION
BEAM_TARGET=$REL_BASE/beams
SRC_TARGET=$REL_BASE/src

mkdir -p $BEAM_TARGET
mkdir -p $SRC_TARGET

cp README.md $REL_BASE
cp Tour.md $REL_BASE
cp code_of_conduct.md $REL_BASE
cp $ALPACA_BEAMS/*.beam $BEAM_TARGET
cp src/* $SRC_TARGET

tar cvzf alpaca.tgz $REL_BASE

