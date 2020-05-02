# A Foolhardy Attempt to Port Golang to 32-bit PowerPC

*Note: the original README.md has been moved [here](README-orig.md).*

Because Golang should be as ubiquitous as C :)

# Resources

A github [issue](https://github.com/golang/go/issues/22885) was created back in 2017.

In the golang-dev thread "how to port golang to a new architecture", Aram Hăvărneanu
[posted a plan](https://groups.google.com/forum/#!msg/golang-dev/SRUK7yJVA0c/JeoCRMwzBwAJ)
for porting Golang:

```
I've done many ports now, so the strategy I use
is this (very simplified):

    1. Add GOOS/GOARCH support to the toolchain

    2. Add some support for GOARCH in cmd/internal/obj
    3. Add some support for GOARCH in cmd/asm
    4. Add some support for GOOS/GOARCH in cmd/link

    5. Iterate through 2-3-4 until you can produse some kind
       of binaries from assembly files. Depending on the specifics
       of GOOS/GOARCH you might, or might not need to use external
       linking.

    6. Once you can produce binaries, thoroughly test them (link
       just assembly programs, without runtime). Basically make
       sure the low-level toolchain works.

    7. Start working on the Go compiler for GOARCH.

    8. Write a minimal alternative runtime for Go. The runtime
       is much too complicated as a first test Go program. Basically
       write your own runtime in assembly that is just stubbed
       out, but can run a good bulk of the programs in go/test.

    9. Once that works well enough, start using the real runtime.
       This requires implementing a lot of assembly, but you can
       use the lessons learned from #8.

    10. Make all the tests in go/test work.
    11. Make all the stdlib tests work. You are still working
        amd64 now, and executing on GOARCH with go_GOOS_GOARCH_exec.

    12. Run bootstrap.bash

    13. Move over the artifacts on GOOS/GOARCH machine.

    14. Make sure make.bash works. You will still likely have
        to fix problems to make this N-generation compiler work.

    15. Make sure all.bash works.

    16. Done.

As you can see, steps 1-14 are done on amd64 (or some other supported
platform), and only step 15 is done on the target architecture.
```

# Log

## 2020/5/2 Sat

Let's start at the beginning:

```
$ cd src
$ cat > build-linux-ppc.sh <<EOF
#!/bin/bash
set -e
export GOOS=linux
export GOARCH=ppc
export GOROOT_FINAL=/opt/go-linux-ppc
./make.bash -v
EOF
$ chmod +x build-linux-ppc.sh
$ ./build-linux-ppc.sh
```

Our first error:

```
$ ./build-linux-ppc.sh 
cmd/go: unsupported GOOS/GOARCH pair linux/ppc
Building Go cmd/dist using /usr/local/go. ()
cmd/dist
go tool dist: unknown $GOARCH ppc
```

The first error comes from `src/cmd/go/internal/work/action.go`, in `func CheckGOOSARCHPair`.

In `src/cmd/dist/build.go`, add `ppc` to the `okgoarch` array.
