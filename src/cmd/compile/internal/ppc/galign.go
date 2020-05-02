// Copyright 2009 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ppc

import (
	"cmd/compile/internal/gc"
	"cmd/internal/obj/ppc"
	"cmd/internal/objabi"
)

func Init(arch *gc.Arch) {
	arch.LinkArch = &ppc.Linkppc
	arch.REGSP = ppc.REGSP
	arch.MAXWIDTH = 1 << 32

	arch.ZeroRange = zerorange
	arch.Ginsnop = ginsnop
	arch.Ginsnopdefer = ginsnopdefer

	arch.SSAMarkMoves = ssaMarkMoves
	arch.SSAGenValue = ssaGenValue
	arch.SSAGenBlock = ssaGenBlock
}
