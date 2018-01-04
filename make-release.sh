#!/bin/bash

# If travis-ci is building a tag then use that as the version, otherwise mark
# this release with the hash from travis-ci or let the CLI override VERSION
# entirely:
VERSION=${VERSION:-${TRAVIS_TAG:-${TRAVIS_COMMIT:-unversioned}}_${TRAVIS_OTP_RELEASE}}

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

tar cvzf alpaca_$TRAVIS_OTP_RELEASE.tgz $REL_BASE

