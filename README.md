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

Next failure:

```
Building packages and commands for target, linux/ppc.
cmd/go: unsupported GOOS/GOARCH pair linux/ppc
go tool dist: FAILED: /home/cell/github/pepaslabs/go-ppc/pkg/tool/linux_amd64/go_bootstrap install -gcflags=all= -ldflags=all= -v std cmd: exit status 2
```

`CheckGOOSARCHPair` checks the map `OSArchSupportsCgo` in `src/cmd/go/internal/cfg/zosarch.go`.

We need to add `"linux/ppc": true` to this map, but the first line of the file notes *Code generated by go tool dist; DO NOT EDIT.*.

`zosarch.go` is generated by the function `mkzosarch` in `src/cmd/dist/buildgo.go`.

Running `go tool dist` gets us:

```
$ go tool dist
usage: go tool dist [command]
Commands are:

banner         print installation banner
bootstrap      rebuild everything
clean          deletes all built files
env [-p]       print environment (-p: include $PATH)
install [dir]  install individual directory
list [-json]   list all supported platforms
test [-h]      run Go test(s)
version        print Go version

All commands take -v flags to emit extra information.
```

Let's try `go tool dist bootstrap`:

```
$ go tool dist bootstrap -v
go tool dist: mkdir /usr/local/go/pkg/obj/go-build: permission denied
```

Perhaps as root?

```
# go tool dist bootstrap -v
Building Go toolchain1 using /root/go1.4.
go tool dist: FAILED: /root/go1.4/bin/go install -gcflags=-l -tags=math_big_pure_go compiler_bootstrap -v bootstrap/cmd/...: fork/exec /root/go1.4/bin/go: no such file or directory
```

Perhaps I just need to run `make.bash`?

```
$ ./make.bash 
Building Go cmd/dist using /usr/local/go. (go1.14.2 linux/amd64)
Building Go toolchain1 using /usr/local/go.
Building Go bootstrap cmd/go (go_bootstrap) using Go toolchain1.
Building Go toolchain2 using go_bootstrap and Go toolchain1.
Building Go toolchain3 using go_bootstrap and Go toolchain2.
Building packages and commands for linux/amd64.
---
Installed Go for linux/amd64 in /home/cell/github/pepaslabs/go-ppc
Installed commands in /home/cell/github/pepaslabs/go-ppc/bin
```

That seemed to work...

But zosarch.go still hasn't been updated:

```
$ cat cmd/go/internal/cfg/zosarch.go | grep ppc
        "aix/ppc64": true,
        "linux/ppc64": false,
        "linux/ppc64le": true,
```

Welp, let's try editing `zosarch.go` by hand.

```
$ ./build-linux-ppc.sh
...
Building packages and commands for target, linux/ppc.
cmd/go: unsupported GOOS/GOARCH pair linux/ppc
go tool dist: FAILED: /home/cell/github/pepaslabs/go-ppc/pkg/tool/linux_amd64/go_bootstrap install -gcflags=all= -ldflags=all= -v std cmd: exit status 2
```

Hmm.

Ok, so my current `go` binary doesn't support `linux/ppc`, and it is what is failing:

```
$ go tool dist list | grep ppc
aix/ppc64
linux/ppc64
linux/ppc64le
```

So first I need to build a `go` which doesn't abort as soon as it sees a `linux/ppc` `GOOS/GOARCH`.

Let's try `GOOS=linux GOARCH=ppc ./bootstrap.bash`.

```
$ GOOS=linux GOARCH=ppc ./bootstrap.bash 
#### Copying to ../../go-linux-ppc-bootstrap

#### Cleaning ../../go-linux-ppc-bootstrap
Removing VERSION.cache
Removing bin/
Removing pkg/
Removing src/cmd/cgo/zdefaultcc.go
Removing src/cmd/dist/dist
Removing src/cmd/go/internal/cfg/zdefaultcc.go
Removing src/cmd/go/internal/cfg/zosarch.go
Removing src/cmd/internal/objabi/zbootstrap.go
Removing src/go/build/zcgo.go
Removing src/runtime/internal/sys/zversion.go

#### Building ../../go-linux-ppc-bootstrap

cmd/go: unsupported GOOS/GOARCH pair linux/ppc
Building Go cmd/dist using /usr/local/go. ()
Building Go toolchain1 using /usr/local/go.
Building Go bootstrap cmd/go (go_bootstrap) using Go toolchain1.
Building Go toolchain2 using go_bootstrap and Go toolchain1.
Building Go toolchain3 using go_bootstrap and Go toolchain2.
Building packages and commands for host, linux/amd64.
Building packages and commands for target, linux/ppc.
cmd/go: unsupported GOOS/GOARCH pair linux/ppc
go tool dist: FAILED: /home/cell/github/pepaslabs/go-linux-ppc-bootstrap/pkg/tool/linux_amd64/go_bootstrap install -gcflags=all= -ldflags=all= std cmd: exit status 2
```

Also, `zosarch.go` has been reset and no longer contains `linux/ppc`:

```
$ cat cmd/go/internal/cfg/zosarch.go | grep ppc
        "aix/ppc64": true,
        "linux/ppc64": false,
        "linux/ppc64le": true,
```

Ah, in `src/cmd/dist/build.go`, we see this:

```
// Cannot use go/build directly because cmd/dist for a new release
// builds against an old release's go/build, which may be out of sync.
// To reduce duplication, we generate the list for go/build from this.
//
// We list all supported platforms in this list, so that this is the
// single point of truth for supported platforms. This list is used
// by 'go tool dist list'.
var cgoEnabled = map[string]bool{
```

Now let's try bootstrapping again.

```
$ GOOS=linux GOARCH=ppc ./bootstrap.bash 
../../go-linux-ppc-bootstrap already exists; remove before continuing
```

Ok, let's clean that up and try again.

```
$ rm -rf ../../go-linux-ppc-bootstrap
$ GOOS=linux GOARCH=ppc ./bootstrap.bash 
Building packages and commands for host, linux/amd64.
Building packages and commands for target, linux/ppc.
go tool compile: exit status 2
compile: unknown architecture "ppc"
go tool dist: FAILED: /home/cell/github/pepaslabs/go-linux-ppc-bootstrap/pkg/tool/linux_amd64/go_bootstrap install -gcflags=all= -ldflags=all= std cmd: exit status 1
```

Ok, perhaps I first need to bootstrap `go` for my own platform (with updated `cgoEnabled` map),
and then use that to build `go` for `linux/ppc`.

