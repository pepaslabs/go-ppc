#!/bin/bash
set -e
export GOOS=linux
export GOARCH=ppc
export GOROOT_FINAL=/opt/go-linux-ppc
./make.bash -v
