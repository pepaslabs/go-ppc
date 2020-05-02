// Copyright 2016 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ppc

import (
	"cmd/compile/internal/gc"
	"cmd/compile/internal/logopt"
	"cmd/compile/internal/ssa"
	"cmd/compile/internal/types"
	"cmd/internal/obj"
	"cmd/internal/obj/ppc"
	"cmd/internal/objabi"
	"math"
	"strings"
)

// markMoves marks any MOVXconst ops that need to avoid clobbering flags.
func ssaMarkMoves(s *gc.SSAGenState, b *ssa.Block) {
	//	flive := b.FlagsLiveAtEnd
	//	if b.Control != nil && b.Control.Type.IsFlags() {
	//		flive = true
	//	}
	//	for i := len(b.Values) - 1; i >= 0; i-- {
	//		v := b.Values[i]
	//		if flive && (v.Op == v.Op == ssa.OpPPCMOVDconst) {
	//			// The "mark" is any non-nil Aux value.
	//			v.Aux = v
	//		}
	//		if v.Type.IsFlags() {
	//			flive = false
	//		}
	//		for _, a := range v.Args {
	//			if a.Type.IsFlags() {
	//				flive = true
	//			}
	//		}
	//	}
}

// loadByType returns the load instruction of the given type.
func loadByType(t *types.Type) obj.As {
	if t.IsFloat() {
		switch t.Size() {
		case 4:
			return ppc.AFMOVS
		case 8:
			return ppc.AFMOVD
		}
	} else {
		switch t.Size() {
		case 1:
			if t.IsSigned() {
				return ppc.AMOVB
			} else {
				return ppc.AMOVBZ
			}
		case 2:
			if t.IsSigned() {
				return ppc.AMOVH
			} else {
				return ppc.AMOVHZ
			}
		case 4:
			if t.IsSigned() {
				return ppc.AMOVW
			} else {
				return ppc.AMOVWZ
			}
		case 8:
			return ppc.AMOVD
		}
	}
	panic("bad load type")
}

// storeByType returns the store instruction of the given type.
func storeByType(t *types.Type) obj.As {
	if t.IsFloat() {
		switch t.Size() {
		case 4:
			return ppc.AFMOVS
		case 8:
			return ppc.AFMOVD
		}
	} else {
		switch t.Size() {
		case 1:
			return ppc.AMOVB
		case 2:
			return ppc.AMOVH
		case 4:
			return ppc.AMOVW
		case 8:
			return ppc.AMOVD
		}
	}
	panic("bad store type")
}

func ssaGenValue(s *gc.SSAGenState, v *ssa.Value) {
	switch v.Op {
	case ssa.OpCopy:
		t := v.Type
		if t.IsMemory() {
			return
		}
		x := v.Args[0].Reg()
		y := v.Reg()
		if x != y {
			rt := obj.TYPE_REG
			op := ppc.AMOVD

			if t.IsFloat() {
				op = ppc.AFMOVD
			}
			p := s.Prog(op)
			p.From.Type = rt
			p.From.Reg = x
			p.To.Type = rt
			p.To.Reg = y
		}

	case ssa.OpPPCLoweredMuluhilo:
		// MULHDU	Rarg1, Rarg0, Reg0
		// MULLD	Rarg1, Rarg0, Reg1
		r0 := v.Args[0].Reg()
		r1 := v.Args[1].Reg()
		p := s.Prog(ppc.AMULHDU)
		p.From.Type = obj.TYPE_REG
		p.From.Reg = r1
		p.Reg = r0
		p.To.Type = obj.TYPE_REG
		p.To.Reg = v.Reg0()
		p1 := s.Prog(ppc.AMULLD)
		p1.From.Type = obj.TYPE_REG
		p1.From.Reg = r1
		p1.Reg = r0
		p1.To.Type = obj.TYPE_REG
		p1.To.Reg = v.Reg1()

	case ssa.OpPPCLoweredAdd64Carry:
		// ADDC		Rarg2, -1, Rtmp
		// ADDE		Rarg1, Rarg0, Reg0
		// ADDZE	Rzero, Reg1
		r0 := v.Args[0].Reg()
		r1 := v.Args[1].Reg()
		r2 := v.Args[2].Reg()
		p := s.Prog(ppc.AADDC)
		p.From.Type = obj.TYPE_CONST
		p.From.Offset = -1
		p.Reg = r2
		p.To.Type = obj.TYPE_REG
		p.To.Reg = ppc.REGTMP
		p1 := s.Prog(ppc.AADDE)
		p1.From.Type = obj.TYPE_REG
		p1.From.Reg = r1
		p1.Reg = r0
		p1.To.Type = obj.TYPE_REG
		p1.To.Reg = v.Reg0()
		p2 := s.Prog(ppc.AADDZE)
		p2.From.Type = obj.TYPE_REG
		p2.From.Reg = ppc.REGZERO
		p2.To.Type = obj.TYPE_REG
		p2.To.Reg = v.Reg1()

	case ssa.OpPPCLoweredAtomicAnd8,
		ssa.OpPPCLoweredAtomicOr8:
		// LWSYNC
		// LBAR		(Rarg0), Rtmp
		// AND/OR	Rarg1, Rtmp
		// STBCCC	Rtmp, (Rarg0)
		// BNE		-3(PC)
		r0 := v.Args[0].Reg()
		r1 := v.Args[1].Reg()
		// LWSYNC - Assuming shared data not write-through-required nor
		// caching-inhibited. See Appendix B.2.2.2 in the ISA 2.07b.
		plwsync := s.Prog(ppc.ALWSYNC)
		plwsync.To.Type = obj.TYPE_NONE
		p := s.Prog(ppc.ALBAR)
		p.From.Type = obj.TYPE_MEM
		p.From.Reg = r0
		p.To.Type = obj.TYPE_REG
		p.To.Reg = ppc.REGTMP
		p1 := s.Prog(v.Op.Asm())
		p1.From.Type = obj.TYPE_REG
		p1.From.Reg = r1
		p1.To.Type = obj.TYPE_REG
		p1.To.Reg = ppc.REGTMP
		p2 := s.Prog(ppc.ASTBCCC)
		p2.From.Type = obj.TYPE_REG
		p2.From.Reg = ppc.REGTMP
		p2.To.Type = obj.TYPE_MEM
		p2.To.Reg = r0
		p2.RegTo2 = ppc.REGTMP
		p3 := s.Prog(ppc.ABNE)
		p3.To.Type = obj.TYPE_BRANCH
		gc.Patch(p3, p)

	case ssa.OpPPCLoweredAtomicAdd32,
		ssa.OpPPCLoweredAtomicAdd64:
		// LWSYNC
		// LDAR/LWAR    (Rarg0), Rout
		// ADD		Rarg1, Rout
		// STDCCC/STWCCC Rout, (Rarg0)
		// BNE         -3(PC)
		// MOVW		Rout,Rout (if Add32)
		ld := ppc.ALDAR
		st := ppc.ASTDCCC
		if v.Op == ssa.OpPPCLoweredAtomicAdd32 {
			ld = ppc.ALWAR
			st = ppc.ASTWCCC
		}
		r0 := v.Args[0].Reg()
		r1 := v.Args[1].Reg()
		out := v.Reg0()
		// LWSYNC - Assuming shared data not write-through-required nor
		// caching-inhibited. See Appendix B.2.2.2 in the ISA 2.07b.
		plwsync := s.Prog(ppc.ALWSYNC)
		plwsync.To.Type = obj.TYPE_NONE
		// LDAR or LWAR
		p := s.Prog(ld)
		p.From.Type = obj.TYPE_MEM
		p.From.Reg = r0
		p.To.Type = obj.TYPE_REG
		p.To.Reg = out
		// ADD reg1,out
		p1 := s.Prog(ppc.AADD)
		p1.From.Type = obj.TYPE_REG
		p1.From.Reg = r1
		p1.To.Reg = out
		p1.To.Type = obj.TYPE_REG
		// STDCCC or STWCCC
		p3 := s.Prog(st)
		p3.From.Type = obj.TYPE_REG
		p3.From.Reg = out
		p3.To.Type = obj.TYPE_MEM
		p3.To.Reg = r0
		// BNE retry
		p4 := s.Prog(ppc.ABNE)
		p4.To.Type = obj.TYPE_BRANCH
		gc.Patch(p4, p)

		// Ensure a 32 bit result
		if v.Op == ssa.OpPPCLoweredAtomicAdd32 {
			p5 := s.Prog(ppc.AMOVWZ)
			p5.To.Type = obj.TYPE_REG
			p5.To.Reg = out
			p5.From.Type = obj.TYPE_REG
			p5.From.Reg = out
		}

	case ssa.OpPPCLoweredAtomicExchange32,
		ssa.OpPPCLoweredAtomicExchange64:
		// LWSYNC
		// LDAR/LWAR    (Rarg0), Rout
		// STDCCC/STWCCC Rout, (Rarg0)
		// BNE         -2(PC)
		// ISYNC
		ld := ppc.ALDAR
		st := ppc.ASTDCCC
		if v.Op == ssa.OpPPCLoweredAtomicExchange32 {
			ld = ppc.ALWAR
			st = ppc.ASTWCCC
		}
		r0 := v.Args[0].Reg()
		r1 := v.Args[1].Reg()
		out := v.Reg0()
		// LWSYNC - Assuming shared data not write-through-required nor
		// caching-inhibited. See Appendix B.2.2.2 in the ISA 2.07b.
		plwsync := s.Prog(ppc.ALWSYNC)
		plwsync.To.Type = obj.TYPE_NONE
		// LDAR or LWAR
		p := s.Prog(ld)
		p.From.Type = obj.TYPE_MEM
		p.From.Reg = r0
		p.To.Type = obj.TYPE_REG
		p.To.Reg = out
		// STDCCC or STWCCC
		p1 := s.Prog(st)
		p1.From.Type = obj.TYPE_REG
		p1.From.Reg = r1
		p1.To.Type = obj.TYPE_MEM
		p1.To.Reg = r0
		// BNE retry
		p2 := s.Prog(ppc.ABNE)
		p2.To.Type = obj.TYPE_BRANCH
		gc.Patch(p2, p)
		// ISYNC
		pisync := s.Prog(ppc.AISYNC)
		pisync.To.Type = obj.TYPE_NONE

	case ssa.OpPPCLoweredAtomicLoad8,
		ssa.OpPPCLoweredAtomicLoad32,
		ssa.OpPPCLoweredAtomicLoad64,
		ssa.OpPPCLoweredAtomicLoadPtr:
		// SYNC
		// MOVB/MOVD/MOVW (Rarg0), Rout
		// CMP Rout,Rout
		// BNE 1(PC)
		// ISYNC
		ld := ppc.AMOVD
		cmp := ppc.ACMP
		switch v.Op {
		case ssa.OpPPCLoweredAtomicLoad8:
			ld = ppc.AMOVBZ
		case ssa.OpPPCLoweredAtomicLoad32:
			ld = ppc.AMOVWZ
			cmp = ppc.ACMPW
		}
		arg0 := v.Args[0].Reg()
		out := v.Reg0()
		// SYNC when AuxInt == 1; otherwise, load-acquire
		if v.AuxInt == 1 {
			psync := s.Prog(ppc.ASYNC)
			psync.To.Type = obj.TYPE_NONE
		}
		// Load
		p := s.Prog(ld)
		p.From.Type = obj.TYPE_MEM
		p.From.Reg = arg0
		p.To.Type = obj.TYPE_REG
		p.To.Reg = out
		// CMP
		p1 := s.Prog(cmp)
		p1.From.Type = obj.TYPE_REG
		p1.From.Reg = out
		p1.To.Type = obj.TYPE_REG
		p1.To.Reg = out
		// BNE
		p2 := s.Prog(ppc.ABNE)
		p2.To.Type = obj.TYPE_BRANCH
		// ISYNC
		pisync := s.Prog(ppc.AISYNC)
		pisync.To.Type = obj.TYPE_NONE
		gc.Patch(p2, pisync)

	case ssa.OpPPCLoweredAtomicStore8,
		ssa.OpPPCLoweredAtomicStore32,
		ssa.OpPPCLoweredAtomicStore64:
		// SYNC or LWSYNC
		// MOVB/MOVW/MOVD arg1,(arg0)
		st := ppc.AMOVD
		switch v.Op {
		case ssa.OpPPCLoweredAtomicStore8:
			st = ppc.AMOVB
		case ssa.OpPPCLoweredAtomicStore32:
			st = ppc.AMOVW
		}
		arg0 := v.Args[0].Reg()
		arg1 := v.Args[1].Reg()
		// If AuxInt == 0, LWSYNC (Store-Release), else SYNC
		// SYNC
		syncOp := ppc.ASYNC
		if v.AuxInt == 0 {
			syncOp = ppc.ALWSYNC
		}
		psync := s.Prog(syncOp)
		psync.To.Type = obj.TYPE_NONE
		// Store
		p := s.Prog(st)
		p.To.Type = obj.TYPE_MEM
		p.To.Reg = arg0
		p.From.Type = obj.TYPE_REG
		p.From.Reg = arg1

	case ssa.OpPPCLoweredAtomicCas64,
		ssa.OpPPCLoweredAtomicCas32:
		// LWSYNC
		// loop:
		// LDAR        (Rarg0), MutexHint, Rtmp
		// CMP         Rarg1, Rtmp
		// BNE         fail
		// STDCCC      Rarg2, (Rarg0)
		// BNE         loop
		// LWSYNC      // Only for sequential consistency; not required in CasRel.
		// MOVD        $1, Rout
		// BR          end
		// fail:
		// MOVD        $0, Rout
		// end:
		ld := ppc.ALDAR
		st := ppc.ASTDCCC
		cmp := ppc.ACMP
		if v.Op == ssa.OpPPCLoweredAtomicCas32 {
			ld = ppc.ALWAR
			st = ppc.ASTWCCC
			cmp = ppc.ACMPW
		}
		r0 := v.Args[0].Reg()
		r1 := v.Args[1].Reg()
		r2 := v.Args[2].Reg()
		out := v.Reg0()
		// LWSYNC - Assuming shared data not write-through-required nor
		// caching-inhibited. See Appendix B.2.2.2 in the ISA 2.07b.
		plwsync1 := s.Prog(ppc.ALWSYNC)
		plwsync1.To.Type = obj.TYPE_NONE
		// LDAR or LWAR
		p := s.Prog(ld)
		p.From.Type = obj.TYPE_MEM
		p.From.Reg = r0
		p.To.Type = obj.TYPE_REG
		p.To.Reg = ppc.REGTMP
		// If it is a Compare-and-Swap-Release operation, set the EH field with
		// the release hint.
		if v.AuxInt == 0 {
			p.SetFrom3(obj.Addr{Type: obj.TYPE_CONST, Offset: 0})
		}
		// CMP reg1,reg2
		p1 := s.Prog(cmp)
		p1.From.Type = obj.TYPE_REG
		p1.From.Reg = r1
		p1.To.Reg = ppc.REGTMP
		p1.To.Type = obj.TYPE_REG
		// BNE cas_fail
		p2 := s.Prog(ppc.ABNE)
		p2.To.Type = obj.TYPE_BRANCH
		// STDCCC or STWCCC
		p3 := s.Prog(st)
		p3.From.Type = obj.TYPE_REG
		p3.From.Reg = r2
		p3.To.Type = obj.TYPE_MEM
		p3.To.Reg = r0
		// BNE retry
		p4 := s.Prog(ppc.ABNE)
		p4.To.Type = obj.TYPE_BRANCH
		gc.Patch(p4, p)
		// LWSYNC - Assuming shared data not write-through-required nor
		// caching-inhibited. See Appendix B.2.1.1 in the ISA 2.07b.
		// If the operation is a CAS-Release, then synchronization is not necessary.
		if v.AuxInt != 0 {
			plwsync2 := s.Prog(ppc.ALWSYNC)
			plwsync2.To.Type = obj.TYPE_NONE
		}
		// return true
		p5 := s.Prog(ppc.AMOVD)
		p5.From.Type = obj.TYPE_CONST
		p5.From.Offset = 1
		p5.To.Type = obj.TYPE_REG
		p5.To.Reg = out
		// BR done
		p6 := s.Prog(obj.AJMP)
		p6.To.Type = obj.TYPE_BRANCH
		// return false
		p7 := s.Prog(ppc.AMOVD)
		p7.From.Type = obj.TYPE_CONST
		p7.From.Offset = 0
		p7.To.Type = obj.TYPE_REG
		p7.To.Reg = out
		gc.Patch(p2, p7)
		// done (label)
		p8 := s.Prog(obj.ANOP)
		gc.Patch(p6, p8)

	case ssa.OpPPCLoweredGetClosurePtr:
		// Closure pointer is R11 (already)
		gc.CheckLoweredGetClosurePtr(v)

	case ssa.OpPPCLoweredGetCallerSP:
		// caller's SP is FixedFrameSize below the address of the first arg
		p := s.Prog(ppc.AMOVD)
		p.From.Type = obj.TYPE_ADDR
		p.From.Offset = -gc.Ctxt.FixedFrameSize()
		p.From.Name = obj.NAME_PARAM
		p.To.Type = obj.TYPE_REG
		p.To.Reg = v.Reg()

	case ssa.OpPPCLoweredGetCallerPC:
		p := s.Prog(obj.AGETCALLERPC)
		p.To.Type = obj.TYPE_REG
		p.To.Reg = v.Reg()

	case ssa.OpPPCLoweredRound32F, ssa.OpPPCLoweredRound64F:
		// input is already rounded

	case ssa.OpLoadReg:
		loadOp := loadByType(v.Type)
		p := s.Prog(loadOp)
		gc.AddrAuto(&p.From, v.Args[0])
		p.To.Type = obj.TYPE_REG
		p.To.Reg = v.Reg()

	case ssa.OpStoreReg:
		storeOp := storeByType(v.Type)
		p := s.Prog(storeOp)
		p.From.Type = obj.TYPE_REG
		p.From.Reg = v.Args[0].Reg()
		gc.AddrAuto(&p.To, v)

	case ssa.OpPPCDIVD:
		// For now,
		//
		// cmp arg1, -1
		// be  ahead
		// v = arg0 / arg1
		// b over
		// ahead: v = - arg0
		// over: nop
		r := v.Reg()
		r0 := v.Args[0].Reg()
		r1 := v.Args[1].Reg()

		p := s.Prog(ppc.ACMP)
		p.From.Type = obj.TYPE_REG
		p.From.Reg = r1
		p.To.Type = obj.TYPE_CONST
		p.To.Offset = -1

		pbahead := s.Prog(ppc.ABEQ)
		pbahead.To.Type = obj.TYPE_BRANCH

		p = s.Prog(v.Op.Asm())
		p.From.Type = obj.TYPE_REG
		p.From.Reg = r1
		p.Reg = r0
		p.To.Type = obj.TYPE_REG
		p.To.Reg = r

		pbover := s.Prog(obj.AJMP)
		pbover.To.Type = obj.TYPE_BRANCH

		p = s.Prog(ppc.ANEG)
		p.To.Type = obj.TYPE_REG
		p.To.Reg = r
		p.From.Type = obj.TYPE_REG
		p.From.Reg = r0
		gc.Patch(pbahead, p)

		p = s.Prog(obj.ANOP)
		gc.Patch(pbover, p)

	case ssa.OpPPCDIVW:
		// word-width version of above
		r := v.Reg()
		r0 := v.Args[0].Reg()
		r1 := v.Args[1].Reg()

		p := s.Prog(ppc.ACMPW)
		p.From.Type = obj.TYPE_REG
		p.From.Reg = r1
		p.To.Type = obj.TYPE_CONST
		p.To.Offset = -1

		pbahead := s.Prog(ppc.ABEQ)
		pbahead.To.Type = obj.TYPE_BRANCH

		p = s.Prog(v.Op.Asm())
		p.From.Type = obj.TYPE_REG
		p.From.Reg = r1
		p.Reg = r0
		p.To.Type = obj.TYPE_REG
		p.To.Reg = r

		pbover := s.Prog(obj.AJMP)
		pbover.To.Type = obj.TYPE_BRANCH

		p = s.Prog(ppc.ANEG)
		p.To.Type = obj.TYPE_REG
		p.To.Reg = r
		p.From.Type = obj.TYPE_REG
		p.From.Reg = r0
		gc.Patch(pbahead, p)

		p = s.Prog(obj.ANOP)
		gc.Patch(pbover, p)

	case ssa.OpPPCADD, ssa.OpPPCFADD, ssa.OpPPCFADDS, ssa.OpPPCSUB, ssa.OpPPCFSUB, ssa.OpPPCFSUBS,
		ssa.OpPPCMULLD, ssa.OpPPCMULLW, ssa.OpPPCDIVDU, ssa.OpPPCDIVWU,
		ssa.OpPPCSRAD, ssa.OpPPCSRAW, ssa.OpPPCSRD, ssa.OpPPCSRW, ssa.OpPPCSLD, ssa.OpPPCSLW,
		ssa.OpPPCROTL, ssa.OpPPCROTLW,
		ssa.OpPPCMULHD, ssa.OpPPCMULHW, ssa.OpPPCMULHDU, ssa.OpPPCMULHWU,
		ssa.OpPPCFMUL, ssa.OpPPCFMULS, ssa.OpPPCFDIV, ssa.OpPPCFDIVS, ssa.OpPPCFCPSGN,
		ssa.OpPPCAND, ssa.OpPPCOR, ssa.OpPPCANDN, ssa.OpPPCORN, ssa.OpPPCNOR, ssa.OpPPCXOR, ssa.OpPPCEQV,
		ssa.OpPPCMODUD, ssa.OpPPCMODSD, ssa.OpPPCMODUW, ssa.OpPPCMODSW:
		r := v.Reg()
		r1 := v.Args[0].Reg()
		r2 := v.Args[1].Reg()
		p := s.Prog(v.Op.Asm())
		p.From.Type = obj.TYPE_REG
		p.From.Reg = r2
		p.Reg = r1
		p.To.Type = obj.TYPE_REG
		p.To.Reg = r

	case ssa.OpPPCANDCC, ssa.OpPPCORCC, ssa.OpPPCXORCC:
		r1 := v.Args[0].Reg()
		r2 := v.Args[1].Reg()
		p := s.Prog(v.Op.Asm())
		p.From.Type = obj.TYPE_REG
		p.From.Reg = r2
		p.Reg = r1
		p.To.Type = obj.TYPE_REG
		p.To.Reg = ppc.REGTMP // result is not needed

	case ssa.OpPPCROTLconst, ssa.OpPPCROTLWconst:
		p := s.Prog(v.Op.Asm())
		p.From.Type = obj.TYPE_CONST
		p.From.Offset = v.AuxInt
		p.Reg = v.Args[0].Reg()
		p.To.Type = obj.TYPE_REG
		p.To.Reg = v.Reg()

	case ssa.OpPPCFMADD, ssa.OpPPCFMADDS, ssa.OpPPCFMSUB, ssa.OpPPCFMSUBS:
		r := v.Reg()
		r1 := v.Args[0].Reg()
		r2 := v.Args[1].Reg()
		r3 := v.Args[2].Reg()
		// r = r1*r2 ± r3
		p := s.Prog(v.Op.Asm())
		p.From.Type = obj.TYPE_REG
		p.From.Reg = r1
		p.Reg = r3
		p.SetFrom3(obj.Addr{Type: obj.TYPE_REG, Reg: r2})
		p.To.Type = obj.TYPE_REG
		p.To.Reg = r

	case ssa.OpPPCMaskIfNotCarry:
		r := v.Reg()
		p := s.Prog(v.Op.Asm())
		p.From.Type = obj.TYPE_REG
		p.From.Reg = ppc.REGZERO
		p.To.Type = obj.TYPE_REG
		p.To.Reg = r

	case ssa.OpPPCADDconstForCarry:
		r1 := v.Args[0].Reg()
		p := s.Prog(v.Op.Asm())
		p.Reg = r1
		p.From.Type = obj.TYPE_CONST
		p.From.Offset = v.AuxInt
		p.To.Type = obj.TYPE_REG
		p.To.Reg = ppc.REGTMP // Ignored; this is for the carry effect.

	case ssa.OpPPCNEG, ssa.OpPPCFNEG, ssa.OpPPCFSQRT, ssa.OpPPCFSQRTS, ssa.OpPPCFFLOOR, ssa.OpPPCFTRUNC, ssa.OpPPCFCEIL,
		ssa.OpPPCFCTIDZ, ssa.OpPPCFCTIWZ, ssa.OpPPCFCFID, ssa.OpPPCFCFIDS, ssa.OpPPCFRSP, ssa.OpPPCCNTLZD, ssa.OpPPCCNTLZW,
		ssa.OpPPCPOPCNTD, ssa.OpPPCPOPCNTW, ssa.OpPPCPOPCNTB, ssa.OpPPCMFVSRD, ssa.OpPPCMTVSRD, ssa.OpPPCFABS, ssa.OpPPCFNABS,
		ssa.OpPPCFROUND, ssa.OpPPCCNTTZW, ssa.OpPPCCNTTZD:
		r := v.Reg()
		p := s.Prog(v.Op.Asm())
		p.To.Type = obj.TYPE_REG
		p.To.Reg = r
		p.From.Type = obj.TYPE_REG
		p.From.Reg = v.Args[0].Reg()

	case ssa.OpPPCADDconst, ssa.OpPPCANDconst, ssa.OpPPCORconst, ssa.OpPPCXORconst,
		ssa.OpPPCSRADconst, ssa.OpPPCSRAWconst, ssa.OpPPCSRDconst, ssa.OpPPCSRWconst, ssa.OpPPCSLDconst, ssa.OpPPCSLWconst:
		p := s.Prog(v.Op.Asm())
		p.Reg = v.Args[0].Reg()
		p.From.Type = obj.TYPE_CONST
		p.From.Offset = v.AuxInt
		p.To.Type = obj.TYPE_REG
		p.To.Reg = v.Reg()

	case ssa.OpPPCANDCCconst:
		p := s.Prog(v.Op.Asm())
		p.Reg = v.Args[0].Reg()
		p.From.Type = obj.TYPE_CONST
		p.From.Offset = v.AuxInt
		p.To.Type = obj.TYPE_REG
		p.To.Reg = ppc.REGTMP // discard result

	case ssa.OpPPCMOVDaddr:
		switch v.Aux.(type) {
		default:
			v.Fatalf("aux in MOVDaddr is of unknown type %T", v.Aux)
		case nil:
			// If aux offset and aux int are both 0, and the same
			// input and output regs are used, no instruction
			// needs to be generated, since it would just be
			// addi rx, rx, 0.
			if v.AuxInt != 0 || v.Args[0].Reg() != v.Reg() {
				p := s.Prog(ppc.AMOVD)
				p.From.Type = obj.TYPE_ADDR
				p.From.Reg = v.Args[0].Reg()
				p.From.Offset = v.AuxInt
				p.To.Type = obj.TYPE_REG
				p.To.Reg = v.Reg()
			}

		case *obj.LSym, *gc.Node:
			p := s.Prog(ppc.AMOVD)
			p.From.Type = obj.TYPE_ADDR
			p.From.Reg = v.Args[0].Reg()
			p.To.Type = obj.TYPE_REG
			p.To.Reg = v.Reg()
			gc.AddAux(&p.From, v)

		}

	case ssa.OpPPCMOVDconst:
		p := s.Prog(v.Op.Asm())
		p.From.Type = obj.TYPE_CONST
		p.From.Offset = v.AuxInt
		p.To.Type = obj.TYPE_REG
		p.To.Reg = v.Reg()

	case ssa.OpPPCFMOVDconst, ssa.OpPPCFMOVSconst:
		p := s.Prog(v.Op.Asm())
		p.From.Type = obj.TYPE_FCONST
		p.From.Val = math.Float64frombits(uint64(v.AuxInt))
		p.To.Type = obj.TYPE_REG
		p.To.Reg = v.Reg()

	case ssa.OpPPCFCMPU, ssa.OpPPCCMP, ssa.OpPPCCMPW, ssa.OpPPCCMPU, ssa.OpPPCCMPWU:
		p := s.Prog(v.Op.Asm())
		p.From.Type = obj.TYPE_REG
		p.From.Reg = v.Args[0].Reg()
		p.To.Type = obj.TYPE_REG
		p.To.Reg = v.Args[1].Reg()

	case ssa.OpPPCCMPconst, ssa.OpPPCCMPUconst, ssa.OpPPCCMPWconst, ssa.OpPPCCMPWUconst:
		p := s.Prog(v.Op.Asm())
		p.From.Type = obj.TYPE_REG
		p.From.Reg = v.Args[0].Reg()
		p.To.Type = obj.TYPE_CONST
		p.To.Offset = v.AuxInt

	case ssa.OpPPCMOVBreg, ssa.OpPPCMOVBZreg, ssa.OpPPCMOVHreg, ssa.OpPPCMOVHZreg, ssa.OpPPCMOVWreg, ssa.OpPPCMOVWZreg:
		// Shift in register to required size
		p := s.Prog(v.Op.Asm())
		p.From.Type = obj.TYPE_REG
		p.From.Reg = v.Args[0].Reg()
		p.To.Reg = v.Reg()
		p.To.Type = obj.TYPE_REG

	case ssa.OpPPCMOVDload:

		// MOVDload uses a DS instruction which requires the offset value of the data to be a multiple of 4.
		// For offsets known at compile time, a MOVDload won't be selected, but in the case of a go.string,
		// the offset is not known until link time. If the load of a go.string uses relocation for the
		// offset field of the instruction, and if the offset is not aligned to 4, then a link error will occur.
		// To avoid this problem, the full address of the go.string is computed and loaded into the base register,
		// and that base register is used for the MOVDload using a 0 offset. This problem can only occur with
		// go.string types because other types will have proper alignment.

		gostring := false
		switch n := v.Aux.(type) {
		case *obj.LSym:
			gostring = strings.HasPrefix(n.Name, "go.string.")
		}
		if gostring {
			// Generate full addr of the go.string const
			// including AuxInt
			p := s.Prog(ppc.AMOVD)
			p.From.Type = obj.TYPE_ADDR
			p.From.Reg = v.Args[0].Reg()
			gc.AddAux(&p.From, v)
			p.To.Type = obj.TYPE_REG
			p.To.Reg = v.Reg()
			// Load go.string using 0 offset
			p = s.Prog(v.Op.Asm())
			p.From.Type = obj.TYPE_MEM
			p.From.Reg = v.Reg()
			p.To.Type = obj.TYPE_REG
			p.To.Reg = v.Reg()
			break
		}
		// Not a go.string, generate a normal load
		fallthrough

	case ssa.OpPPCMOVWload, ssa.OpPPCMOVHload, ssa.OpPPCMOVWZload, ssa.OpPPCMOVBZload, ssa.OpPPCMOVHZload, ssa.OpPPCFMOVDload, ssa.OpPPCFMOVSload:
		p := s.Prog(v.Op.Asm())
		p.From.Type = obj.TYPE_MEM
		p.From.Reg = v.Args[0].Reg()
		gc.AddAux(&p.From, v)
		p.To.Type = obj.TYPE_REG
		p.To.Reg = v.Reg()

	case ssa.OpPPCMOVDBRload, ssa.OpPPCMOVWBRload, ssa.OpPPCMOVHBRload:
		p := s.Prog(v.Op.Asm())
		p.From.Type = obj.TYPE_MEM
		p.From.Reg = v.Args[0].Reg()
		p.To.Type = obj.TYPE_REG
		p.To.Reg = v.Reg()

	case ssa.OpPPCMOVDBRstore, ssa.OpPPCMOVWBRstore, ssa.OpPPCMOVHBRstore:
		p := s.Prog(v.Op.Asm())
		p.To.Type = obj.TYPE_MEM
		p.To.Reg = v.Args[0].Reg()
		p.From.Type = obj.TYPE_REG
		p.From.Reg = v.Args[1].Reg()

	case ssa.OpPPCMOVDloadidx, ssa.OpPPCMOVWloadidx, ssa.OpPPCMOVHloadidx, ssa.OpPPCMOVWZloadidx,
		ssa.OpPPCMOVBZloadidx, ssa.OpPPCMOVHZloadidx, ssa.OpPPCFMOVDloadidx, ssa.OpPPCFMOVSloadidx,
		ssa.OpPPCMOVDBRloadidx, ssa.OpPPCMOVWBRloadidx, ssa.OpPPCMOVHBRloadidx:
		p := s.Prog(v.Op.Asm())
		p.From.Type = obj.TYPE_MEM
		p.From.Reg = v.Args[0].Reg()
		p.From.Index = v.Args[1].Reg()
		p.To.Type = obj.TYPE_REG
		p.To.Reg = v.Reg()

	case ssa.OpPPCMOVDstorezero, ssa.OpPPCMOVWstorezero, ssa.OpPPCMOVHstorezero, ssa.OpPPCMOVBstorezero:
		p := s.Prog(v.Op.Asm())
		p.From.Type = obj.TYPE_REG
		p.From.Reg = ppc.REGZERO
		p.To.Type = obj.TYPE_MEM
		p.To.Reg = v.Args[0].Reg()
		gc.AddAux(&p.To, v)

	case ssa.OpPPCMOVDstore, ssa.OpPPCMOVWstore, ssa.OpPPCMOVHstore, ssa.OpPPCMOVBstore, ssa.OpPPCFMOVDstore, ssa.OpPPCFMOVSstore:
		p := s.Prog(v.Op.Asm())
		p.From.Type = obj.TYPE_REG
		p.From.Reg = v.Args[1].Reg()
		p.To.Type = obj.TYPE_MEM
		p.To.Reg = v.Args[0].Reg()
		gc.AddAux(&p.To, v)

	case ssa.OpPPCMOVDstoreidx, ssa.OpPPCMOVWstoreidx, ssa.OpPPCMOVHstoreidx, ssa.OpPPCMOVBstoreidx,
		ssa.OpPPCFMOVDstoreidx, ssa.OpPPCFMOVSstoreidx, ssa.OpPPCMOVDBRstoreidx, ssa.OpPPCMOVWBRstoreidx,
		ssa.OpPPCMOVHBRstoreidx:
		p := s.Prog(v.Op.Asm())
		p.From.Type = obj.TYPE_REG
		p.From.Reg = v.Args[2].Reg()
		p.To.Index = v.Args[1].Reg()
		p.To.Type = obj.TYPE_MEM
		p.To.Reg = v.Args[0].Reg()

	case ssa.OpPPCISEL, ssa.OpPPCISELB:
		// ISEL, ISELB
		// AuxInt value indicates condition: 0=LT 1=GT 2=EQ 4=GE 5=LE 6=NE
		// ISEL only accepts 0, 1, 2 condition values but the others can be
		// achieved by swapping operand order.
		// arg0 ? arg1 : arg2 with conditions LT, GT, EQ
		// arg0 ? arg2 : arg1 for conditions GE, LE, NE
		// ISELB is used when a boolean result is needed, returning 0 or 1
		p := s.Prog(ppc.AISEL)
		p.To.Type = obj.TYPE_REG
		p.To.Reg = v.Reg()
		// For ISELB, boolean result 0 or 1. Use R0 for 0 operand to avoid load.
		r := obj.Addr{Type: obj.TYPE_REG, Reg: ppc.REG_R0}
		if v.Op == ssa.OpPPCISEL {
			r.Reg = v.Args[1].Reg()
		}
		// AuxInt values 4,5,6 implemented with reverse operand order from 0,1,2
		if v.AuxInt > 3 {
			p.Reg = r.Reg
			p.SetFrom3(obj.Addr{Type: obj.TYPE_REG, Reg: v.Args[0].Reg()})
		} else {
			p.Reg = v.Args[0].Reg()
			p.SetFrom3(r)
		}
		p.From.Type = obj.TYPE_CONST
		p.From.Offset = v.AuxInt & 3

	case ssa.OpPPCLoweredQuadZero, ssa.OpPPCLoweredQuadZeroShort:
		// The LoweredQuad code generation
		// generates STXV instructions on
		// power9. The Short variation is used
		// if no loop is generated.

		// sizes >= 64 generate a loop as follows:

		// Set up loop counter in CTR, used by BC
		// XXLXOR clears VS32
		//       XXLXOR VS32,VS32,VS32
		//       MOVD len/64,REG_TMP
		//       MOVD REG_TMP,CTR
		//       loop:
		//       STXV VS32,0(R20)
		//       STXV VS32,16(R20)
		//       STXV VS32,32(R20)
		//       STXV VS32,48(R20)
		//       ADD  $64,R20
		//       BC   16, 0, loop

		// Bytes per iteration
		ctr := v.AuxInt / 64

		// Remainder bytes
		rem := v.AuxInt % 64

		// Only generate a loop if there is more
		// than 1 iteration.
		if ctr > 1 {
			// Set up VS32 (V0) to hold 0s
			p := s.Prog(ppc.AXXLXOR)
			p.From.Type = obj.TYPE_REG
			p.From.Reg = ppc.REG_VS32
			p.To.Type = obj.TYPE_REG
			p.To.Reg = ppc.REG_VS32
			p.Reg = ppc.REG_VS32

			// Set up CTR loop counter
			p = s.Prog(ppc.AMOVD)
			p.From.Type = obj.TYPE_CONST
			p.From.Offset = ctr
			p.To.Type = obj.TYPE_REG
			p.To.Reg = ppc.REGTMP

			p = s.Prog(ppc.AMOVD)
			p.From.Type = obj.TYPE_REG
			p.From.Reg = ppc.REGTMP
			p.To.Type = obj.TYPE_REG
			p.To.Reg = ppc.REG_CTR

			// Don't generate padding for
			// loops with few iterations.
			if ctr > 3 {
				p = s.Prog(obj.APCALIGN)
				p.From.Type = obj.TYPE_CONST
				p.From.Offset = 16
			}

			// generate 4 STXVs to zero 64 bytes
			var top *obj.Prog

			p = s.Prog(ppc.ASTXV)
			p.From.Type = obj.TYPE_REG
			p.From.Reg = ppc.REG_VS32
			p.To.Type = obj.TYPE_MEM
			p.To.Reg = v.Args[0].Reg()

			//  Save the top of loop
			if top == nil {
				top = p
			}
			p = s.Prog(ppc.ASTXV)
			p.From.Type = obj.TYPE_REG
			p.From.Reg = ppc.REG_VS32
			p.To.Type = obj.TYPE_MEM
			p.To.Reg = v.Args[0].Reg()
			p.To.Offset = 16

			p = s.Prog(ppc.ASTXV)
			p.From.Type = obj.TYPE_REG
			p.From.Reg = ppc.REG_VS32
			p.To.Type = obj.TYPE_MEM
			p.To.Reg = v.Args[0].Reg()
			p.To.Offset = 32

			p = s.Prog(ppc.ASTXV)
			p.From.Type = obj.TYPE_REG
			p.From.Reg = ppc.REG_VS32
			p.To.Type = obj.TYPE_MEM
			p.To.Reg = v.Args[0].Reg()
			p.To.Offset = 48

			// Increment address for the
			// 64 bytes just zeroed.
			p = s.Prog(ppc.AADD)
			p.Reg = v.Args[0].Reg()
			p.From.Type = obj.TYPE_CONST
			p.From.Offset = 64
			p.To.Type = obj.TYPE_REG
			p.To.Reg = v.Args[0].Reg()

			// Branch back to top of loop
			// based on CTR
			// BC with BO_BCTR generates bdnz
			p = s.Prog(ppc.ABC)
			p.From.Type = obj.TYPE_CONST
			p.From.Offset = ppc.BO_BCTR
			p.Reg = ppc.REG_R0
			p.To.Type = obj.TYPE_BRANCH
			gc.Patch(p, top)
		}
		// When ctr == 1 the loop was not generated but
		// there are at least 64 bytes to clear, so add
		// that to the remainder to generate the code
		// to clear those doublewords
		if ctr == 1 {
			rem += 64
		}

		// Clear the remainder starting at offset zero
		offset := int64(0)

		if rem >= 16 && ctr <= 1 {
			// If the XXLXOR hasn't already been
			// generated, do it here to initialize
			// VS32 (V0) to 0.
			p := s.Prog(ppc.AXXLXOR)
			p.From.Type = obj.TYPE_REG
			p.From.Reg = ppc.REG_VS32
			p.To.Type = obj.TYPE_REG
			p.To.Reg = ppc.REG_VS32
			p.Reg = ppc.REG_VS32
		}
		// Generate STXV for 32 or 64
		// bytes.
		for rem >= 32 {
			p := s.Prog(ppc.ASTXV)
			p.From.Type = obj.TYPE_REG
			p.From.Reg = ppc.REG_VS32
			p.To.Type = obj.TYPE_MEM
			p.To.Reg = v.Args[0].Reg()
			p.To.Offset = offset

			p = s.Prog(ppc.ASTXV)
			p.From.Type = obj.TYPE_REG
			p.From.Reg = ppc.REG_VS32
			p.To.Type = obj.TYPE_MEM
			p.To.Reg = v.Args[0].Reg()
			p.To.Offset = offset + 16
			offset += 32
			rem -= 32
		}
		// Generate 16 bytes
		if rem >= 16 {
			p := s.Prog(ppc.ASTXV)
			p.From.Type = obj.TYPE_REG
			p.From.Reg = ppc.REG_VS32
			p.To.Type = obj.TYPE_MEM
			p.To.Reg = v.Args[0].Reg()
			p.To.Offset = offset
			offset += 16
			rem -= 16
		}

		// first clear as many doublewords as possible
		// then clear remaining sizes as available
		for rem > 0 {
			op, size := ppc.AMOVB, int64(1)
			switch {
			case rem >= 8:
				op, size = ppc.AMOVD, 8
			case rem >= 4:
				op, size = ppc.AMOVW, 4
			case rem >= 2:
				op, size = ppc.AMOVH, 2
			}
			p := s.Prog(op)
			p.From.Type = obj.TYPE_REG
			p.From.Reg = ppc.REG_R0
			p.To.Type = obj.TYPE_MEM
			p.To.Reg = v.Args[0].Reg()
			p.To.Offset = offset
			rem -= size
			offset += size
		}

	case ssa.OpPPCLoweredZero, ssa.OpPPCLoweredZeroShort:

		// Unaligned data doesn't hurt performance
		// for these instructions on power8.

		// For sizes >= 64 generate a loop as follows:

		// Set up loop counter in CTR, used by BC
		//       XXLXOR VS32,VS32,VS32
		//	 MOVD len/32,REG_TMP
		//	 MOVD REG_TMP,CTR
		//       MOVD $16,REG_TMP
		//	 loop:
		//	 STXVD2X VS32,(R0)(R20)
		//	 STXVD2X VS32,(R31)(R20)
		//	 ADD  $32,R20
		//	 BC   16, 0, loop
		//
		// any remainder is done as described below

		// for sizes < 64 bytes, first clear as many doublewords as possible,
		// then handle the remainder
		//	MOVD R0,(R20)
		//	MOVD R0,8(R20)
		// .... etc.
		//
		// the remainder bytes are cleared using one or more
		// of the following instructions with the appropriate
		// offsets depending which instructions are needed
		//
		//	MOVW R0,n1(R20)	4 bytes
		//	MOVH R0,n2(R20)	2 bytes
		//	MOVB R0,n3(R20)	1 byte
		//
		// 7 bytes: MOVW, MOVH, MOVB
		// 6 bytes: MOVW, MOVH
		// 5 bytes: MOVW, MOVB
		// 3 bytes: MOVH, MOVB

		// each loop iteration does 32 bytes
		ctr := v.AuxInt / 32

		// remainder bytes
		rem := v.AuxInt % 32

		// only generate a loop if there is more
		// than 1 iteration.
		if ctr > 1 {
			// Set up VS32 (V0) to hold 0s
			p := s.Prog(ppc.AXXLXOR)
			p.From.Type = obj.TYPE_REG
			p.From.Reg = ppc.REG_VS32
			p.To.Type = obj.TYPE_REG
			p.To.Reg = ppc.REG_VS32
			p.Reg = ppc.REG_VS32

			// Set up CTR loop counter
			p = s.Prog(ppc.AMOVD)
			p.From.Type = obj.TYPE_CONST
			p.From.Offset = ctr
			p.To.Type = obj.TYPE_REG
			p.To.Reg = ppc.REGTMP

			p = s.Prog(ppc.AMOVD)
			p.From.Type = obj.TYPE_REG
			p.From.Reg = ppc.REGTMP
			p.To.Type = obj.TYPE_REG
			p.To.Reg = ppc.REG_CTR

			// Set up R31 to hold index value 16
			p = s.Prog(ppc.AMOVD)
			p.From.Type = obj.TYPE_CONST
			p.From.Offset = 16
			p.To.Type = obj.TYPE_REG
			p.To.Reg = ppc.REGTMP

			// Don't add padding for alignment
			// with few loop iterations.
			if ctr > 3 {
				p = s.Prog(obj.APCALIGN)
				p.From.Type = obj.TYPE_CONST
				p.From.Offset = 16
			}

			// generate 2 STXVD2Xs to store 16 bytes
			// when this is a loop then the top must be saved
			var top *obj.Prog
			// This is the top of loop

			p = s.Prog(ppc.ASTXVD2X)
			p.From.Type = obj.TYPE_REG
			p.From.Reg = ppc.REG_VS32
			p.To.Type = obj.TYPE_MEM
			p.To.Reg = v.Args[0].Reg()
			p.To.Index = ppc.REGZERO
			// Save the top of loop
			if top == nil {
				top = p
			}
			p = s.Prog(ppc.ASTXVD2X)
			p.From.Type = obj.TYPE_REG
			p.From.Reg = ppc.REG_VS32
			p.To.Type = obj.TYPE_MEM
			p.To.Reg = v.Args[0].Reg()
			p.To.Index = ppc.REGTMP

			// Increment address for the
			// 4 doublewords just zeroed.
			p = s.Prog(ppc.AADD)
			p.Reg = v.Args[0].Reg()
			p.From.Type = obj.TYPE_CONST
			p.From.Offset = 32
			p.To.Type = obj.TYPE_REG
			p.To.Reg = v.Args[0].Reg()

			// Branch back to top of loop
			// based on CTR
			// BC with BO_BCTR generates bdnz
			p = s.Prog(ppc.ABC)
			p.From.Type = obj.TYPE_CONST
			p.From.Offset = ppc.BO_BCTR
			p.Reg = ppc.REG_R0
			p.To.Type = obj.TYPE_BRANCH
			gc.Patch(p, top)
		}

		// when ctr == 1 the loop was not generated but
		// there are at least 32 bytes to clear, so add
		// that to the remainder to generate the code
		// to clear those doublewords
		if ctr == 1 {
			rem += 32
		}

		// clear the remainder starting at offset zero
		offset := int64(0)

		// first clear as many doublewords as possible
		// then clear remaining sizes as available
		for rem > 0 {
			op, size := ppc.AMOVB, int64(1)
			switch {
			case rem >= 8:
				op, size = ppc.AMOVD, 8
			case rem >= 4:
				op, size = ppc.AMOVW, 4
			case rem >= 2:
				op, size = ppc.AMOVH, 2
			}
			p := s.Prog(op)
			p.From.Type = obj.TYPE_REG
			p.From.Reg = ppc.REG_R0
			p.To.Type = obj.TYPE_MEM
			p.To.Reg = v.Args[0].Reg()
			p.To.Offset = offset
			rem -= size
			offset += size
		}

	case ssa.OpPPCLoweredMove, ssa.OpPPCLoweredMoveShort:

		bytesPerLoop := int64(32)
		// This will be used when moving more
		// than 8 bytes.  Moves start with
		// as many 8 byte moves as possible, then
		// 4, 2, or 1 byte(s) as remaining.  This will
		// work and be efficient for power8 or later.
		// If there are 64 or more bytes, then a
		// loop is generated to move 32 bytes and
		// update the src and dst addresses on each
		// iteration. When < 64 bytes, the appropriate
		// number of moves are generated based on the
		// size.
		// When moving >= 64 bytes a loop is used
		//	MOVD len/32,REG_TMP
		//	MOVD REG_TMP,CTR
		//	MOVD $16,REG_TMP
		// top:
		//	LXVD2X (R0)(R21),VS32
		//	LXVD2X (R31)(R21),VS33
		//	ADD $32,R21
		//	STXVD2X VS32,(R0)(R20)
		//	STXVD2X VS33,(R31)(R20)
		//	ADD $32,R20
		//	BC 16,0,top
		// Bytes not moved by this loop are moved
		// with a combination of the following instructions,
		// starting with the largest sizes and generating as
		// many as needed, using the appropriate offset value.
		//	MOVD  n(R21),R31
		//	MOVD  R31,n(R20)
		//	MOVW  n1(R21),R31
		//	MOVW  R31,n1(R20)
		//	MOVH  n2(R21),R31
		//	MOVH  R31,n2(R20)
		//	MOVB  n3(R21),R31
		//	MOVB  R31,n3(R20)

		// Each loop iteration moves 32 bytes
		ctr := v.AuxInt / bytesPerLoop

		// Remainder after the loop
		rem := v.AuxInt % bytesPerLoop

		dstReg := v.Args[0].Reg()
		srcReg := v.Args[1].Reg()

		// The set of registers used here, must match the clobbered reg list
		// in PPC64Ops.go.
		offset := int64(0)

		// top of the loop
		var top *obj.Prog
		// Only generate looping code when loop counter is > 1 for >= 64 bytes
		if ctr > 1 {
			// Set up the CTR
			p := s.Prog(ppc.AMOVD)
			p.From.Type = obj.TYPE_CONST
			p.From.Offset = ctr
			p.To.Type = obj.TYPE_REG
			p.To.Reg = ppc.REGTMP

			p = s.Prog(ppc.AMOVD)
			p.From.Type = obj.TYPE_REG
			p.From.Reg = ppc.REGTMP
			p.To.Type = obj.TYPE_REG
			p.To.Reg = ppc.REG_CTR

			// Use REGTMP as index reg
			p = s.Prog(ppc.AMOVD)
			p.From.Type = obj.TYPE_CONST
			p.From.Offset = 16
			p.To.Type = obj.TYPE_REG
			p.To.Reg = ppc.REGTMP

			// Don't adding padding for
			// alignment with small iteration
			// counts.
			if ctr > 3 {
				p = s.Prog(obj.APCALIGN)
				p.From.Type = obj.TYPE_CONST
				p.From.Offset = 16
			}

			// Generate 16 byte loads and stores.
			// Use temp register for index (16)
			// on the second one.

			p = s.Prog(ppc.ALXVD2X)
			p.From.Type = obj.TYPE_MEM
			p.From.Reg = srcReg
			p.From.Index = ppc.REGZERO
			p.To.Type = obj.TYPE_REG
			p.To.Reg = ppc.REG_VS32
			if top == nil {
				top = p
			}
			p = s.Prog(ppc.ALXVD2X)
			p.From.Type = obj.TYPE_MEM
			p.From.Reg = srcReg
			p.From.Index = ppc.REGTMP
			p.To.Type = obj.TYPE_REG
			p.To.Reg = ppc.REG_VS33

			// increment the src reg for next iteration
			p = s.Prog(ppc.AADD)
			p.Reg = srcReg
			p.From.Type = obj.TYPE_CONST
			p.From.Offset = bytesPerLoop
			p.To.Type = obj.TYPE_REG
			p.To.Reg = srcReg

			// generate 16 byte stores
			p = s.Prog(ppc.ASTXVD2X)
			p.From.Type = obj.TYPE_REG
			p.From.Reg = ppc.REG_VS32
			p.To.Type = obj.TYPE_MEM
			p.To.Reg = dstReg
			p.To.Index = ppc.REGZERO

			p = s.Prog(ppc.ASTXVD2X)
			p.From.Type = obj.TYPE_REG
			p.From.Reg = ppc.REG_VS33
			p.To.Type = obj.TYPE_MEM
			p.To.Reg = dstReg
			p.To.Index = ppc.REGTMP

			// increment the dst reg for next iteration
			p = s.Prog(ppc.AADD)
			p.Reg = dstReg
			p.From.Type = obj.TYPE_CONST
			p.From.Offset = bytesPerLoop
			p.To.Type = obj.TYPE_REG
			p.To.Reg = dstReg

			// BC with BO_BCTR generates bdnz to branch on nonzero CTR
			// to loop top.
			p = s.Prog(ppc.ABC)
			p.From.Type = obj.TYPE_CONST
			p.From.Offset = ppc.BO_BCTR
			p.Reg = ppc.REG_R0
			p.To.Type = obj.TYPE_BRANCH
			gc.Patch(p, top)

			// srcReg and dstReg were incremented in the loop, so
			// later instructions start with offset 0.
			offset = int64(0)
		}

		// No loop was generated for one iteration, so
		// add 32 bytes to the remainder to move those bytes.
		if ctr == 1 {
			rem += bytesPerLoop
		}

		if rem >= 16 {
			// Generate 16 byte loads and stores.
			// Use temp register for index (value 16)
			// on the second one.
			p := s.Prog(ppc.ALXVD2X)
			p.From.Type = obj.TYPE_MEM
			p.From.Reg = srcReg
			p.From.Index = ppc.REGZERO
			p.To.Type = obj.TYPE_REG
			p.To.Reg = ppc.REG_VS32

			p = s.Prog(ppc.ASTXVD2X)
			p.From.Type = obj.TYPE_REG
			p.From.Reg = ppc.REG_VS32
			p.To.Type = obj.TYPE_MEM
			p.To.Reg = dstReg
			p.To.Index = ppc.REGZERO

			offset = 16
			rem -= 16

			if rem >= 16 {
				// Use REGTMP as index reg
				p := s.Prog(ppc.AMOVD)
				p.From.Type = obj.TYPE_CONST
				p.From.Offset = 16
				p.To.Type = obj.TYPE_REG
				p.To.Reg = ppc.REGTMP

				p = s.Prog(ppc.ALXVD2X)
				p.From.Type = obj.TYPE_MEM
				p.From.Reg = srcReg
				p.From.Index = ppc.REGTMP
				p.To.Type = obj.TYPE_REG
				p.To.Reg = ppc.REG_VS32

				p = s.Prog(ppc.ASTXVD2X)
				p.From.Type = obj.TYPE_REG
				p.From.Reg = ppc.REG_VS32
				p.To.Type = obj.TYPE_MEM
				p.To.Reg = dstReg
				p.To.Index = ppc.REGTMP

				offset = 32
				rem -= 16
			}
		}

		// Generate all the remaining load and store pairs, starting with
		// as many 8 byte moves as possible, then 4, 2, 1.
		for rem > 0 {
			op, size := ppc.AMOVB, int64(1)
			switch {
			case rem >= 8:
				op, size = ppc.AMOVD, 8
			case rem >= 4:
				op, size = ppc.AMOVW, 4
			case rem >= 2:
				op, size = ppc.AMOVH, 2
			}
			// Load
			p := s.Prog(op)
			p.To.Type = obj.TYPE_REG
			p.To.Reg = ppc.REGTMP
			p.From.Type = obj.TYPE_MEM
			p.From.Reg = srcReg
			p.From.Offset = offset

			// Store
			p = s.Prog(op)
			p.From.Type = obj.TYPE_REG
			p.From.Reg = ppc.REGTMP
			p.To.Type = obj.TYPE_MEM
			p.To.Reg = dstReg
			p.To.Offset = offset
			rem -= size
			offset += size
		}

	case ssa.OpPPCLoweredQuadMove, ssa.OpPPCLoweredQuadMoveShort:
		bytesPerLoop := int64(64)
		// This is used when moving more
		// than 8 bytes on power9.  Moves start with
		// as many 8 byte moves as possible, then
		// 4, 2, or 1 byte(s) as remaining.  This will
		// work and be efficient for power8 or later.
		// If there are 64 or more bytes, then a
		// loop is generated to move 32 bytes and
		// update the src and dst addresses on each
		// iteration. When < 64 bytes, the appropriate
		// number of moves are generated based on the
		// size.
		// When moving >= 64 bytes a loop is used
		//      MOVD len/32,REG_TMP
		//      MOVD REG_TMP,CTR
		// top:
		//      LXV 0(R21),VS32
		//      LXV 16(R21),VS33
		//      ADD $32,R21
		//      STXV VS32,0(R20)
		//      STXV VS33,16(R20)
		//      ADD $32,R20
		//      BC 16,0,top
		// Bytes not moved by this loop are moved
		// with a combination of the following instructions,
		// starting with the largest sizes and generating as
		// many as needed, using the appropriate offset value.
		//      MOVD  n(R21),R31
		//      MOVD  R31,n(R20)
		//      MOVW  n1(R21),R31
		//      MOVW  R31,n1(R20)
		//      MOVH  n2(R21),R31
		//      MOVH  R31,n2(R20)
		//      MOVB  n3(R21),R31
		//      MOVB  R31,n3(R20)

		// Each loop iteration moves 32 bytes
		ctr := v.AuxInt / bytesPerLoop

		// Remainder after the loop
		rem := v.AuxInt % bytesPerLoop

		dstReg := v.Args[0].Reg()
		srcReg := v.Args[1].Reg()

		offset := int64(0)

		// top of the loop
		var top *obj.Prog

		// Only generate looping code when loop counter is > 1 for >= 64 bytes
		if ctr > 1 {
			// Set up the CTR
			p := s.Prog(ppc.AMOVD)
			p.From.Type = obj.TYPE_CONST
			p.From.Offset = ctr
			p.To.Type = obj.TYPE_REG
			p.To.Reg = ppc.REGTMP

			p = s.Prog(ppc.AMOVD)
			p.From.Type = obj.TYPE_REG
			p.From.Reg = ppc.REGTMP
			p.To.Type = obj.TYPE_REG
			p.To.Reg = ppc.REG_CTR

			p = s.Prog(obj.APCALIGN)
			p.From.Type = obj.TYPE_CONST
			p.From.Offset = 16

			// Generate 16 byte loads and stores.
			p = s.Prog(ppc.ALXV)
			p.From.Type = obj.TYPE_MEM
			p.From.Reg = srcReg
			p.From.Offset = offset
			p.To.Type = obj.TYPE_REG
			p.To.Reg = ppc.REG_VS32
			if top == nil {
				top = p
			}
			p = s.Prog(ppc.ALXV)
			p.From.Type = obj.TYPE_MEM
			p.From.Reg = srcReg
			p.From.Offset = offset + 16
			p.To.Type = obj.TYPE_REG
			p.To.Reg = ppc.REG_VS33

			// generate 16 byte stores
			p = s.Prog(ppc.ASTXV)
			p.From.Type = obj.TYPE_REG
			p.From.Reg = ppc.REG_VS32
			p.To.Type = obj.TYPE_MEM
			p.To.Reg = dstReg
			p.To.Offset = offset

			p = s.Prog(ppc.ASTXV)
			p.From.Type = obj.TYPE_REG
			p.From.Reg = ppc.REG_VS33
			p.To.Type = obj.TYPE_MEM
			p.To.Reg = dstReg
			p.To.Offset = offset + 16

			// Generate 16 byte loads and stores.
			p = s.Prog(ppc.ALXV)
			p.From.Type = obj.TYPE_MEM
			p.From.Reg = srcReg
			p.From.Offset = offset + 32
			p.To.Type = obj.TYPE_REG
			p.To.Reg = ppc.REG_VS32

			p = s.Prog(ppc.ALXV)
			p.From.Type = obj.TYPE_MEM
			p.From.Reg = srcReg
			p.From.Offset = offset + 48
			p.To.Type = obj.TYPE_REG
			p.To.Reg = ppc.REG_VS33

			// generate 16 byte stores
			p = s.Prog(ppc.ASTXV)
			p.From.Type = obj.TYPE_REG
			p.From.Reg = ppc.REG_VS32
			p.To.Type = obj.TYPE_MEM
			p.To.Reg = dstReg
			p.To.Offset = offset + 32

			p = s.Prog(ppc.ASTXV)
			p.From.Type = obj.TYPE_REG
			p.From.Reg = ppc.REG_VS33
			p.To.Type = obj.TYPE_MEM
			p.To.Reg = dstReg
			p.To.Offset = offset + 48

			// increment the src reg for next iteration
			p = s.Prog(ppc.AADD)
			p.Reg = srcReg
			p.From.Type = obj.TYPE_CONST
			p.From.Offset = bytesPerLoop
			p.To.Type = obj.TYPE_REG
			p.To.Reg = srcReg

			// increment the dst reg for next iteration
			p = s.Prog(ppc.AADD)
			p.Reg = dstReg
			p.From.Type = obj.TYPE_CONST
			p.From.Offset = bytesPerLoop
			p.To.Type = obj.TYPE_REG
			p.To.Reg = dstReg

			// BC with BO_BCTR generates bdnz to branch on nonzero CTR
			// to loop top.
			p = s.Prog(ppc.ABC)
			p.From.Type = obj.TYPE_CONST
			p.From.Offset = ppc.BO_BCTR
			p.Reg = ppc.REG_R0
			p.To.Type = obj.TYPE_BRANCH
			gc.Patch(p, top)

			// srcReg and dstReg were incremented in the loop, so
			// later instructions start with offset 0.
			offset = int64(0)
		}

		// No loop was generated for one iteration, so
		// add 32 bytes to the remainder to move those bytes.
		if ctr == 1 {
			rem += bytesPerLoop
		}
		if rem >= 32 {
			p := s.Prog(ppc.ALXV)
			p.From.Type = obj.TYPE_MEM
			p.From.Reg = srcReg
			p.To.Type = obj.TYPE_REG
			p.To.Reg = ppc.REG_VS32

			p = s.Prog(ppc.ALXV)
			p.From.Type = obj.TYPE_MEM
			p.From.Reg = srcReg
			p.From.Offset = 16
			p.To.Type = obj.TYPE_REG
			p.To.Reg = ppc.REG_VS33

			p = s.Prog(ppc.ASTXV)
			p.From.Type = obj.TYPE_REG
			p.From.Reg = ppc.REG_VS32
			p.To.Type = obj.TYPE_MEM
			p.To.Reg = dstReg

			p = s.Prog(ppc.ASTXV)
			p.From.Type = obj.TYPE_REG
			p.From.Reg = ppc.REG_VS33
			p.To.Type = obj.TYPE_MEM
			p.To.Reg = dstReg
			p.To.Offset = 16

			offset = 32
			rem -= 32
		}

		if rem >= 16 {
			// Generate 16 byte loads and stores.
			p := s.Prog(ppc.ALXV)
			p.From.Type = obj.TYPE_MEM
			p.From.Reg = srcReg
			p.From.Offset = offset
			p.To.Type = obj.TYPE_REG
			p.To.Reg = ppc.REG_VS32

			p = s.Prog(ppc.ASTXV)
			p.From.Type = obj.TYPE_REG
			p.From.Reg = ppc.REG_VS32
			p.To.Type = obj.TYPE_MEM
			p.To.Reg = dstReg
			p.To.Offset = offset

			offset += 16
			rem -= 16

			if rem >= 16 {
				p := s.Prog(ppc.ALXV)
				p.From.Type = obj.TYPE_MEM
				p.From.Reg = srcReg
				p.From.Offset = offset
				p.To.Type = obj.TYPE_REG
				p.To.Reg = ppc.REG_VS32

				p = s.Prog(ppc.ASTXV)
				p.From.Type = obj.TYPE_REG
				p.From.Reg = ppc.REG_VS32
				p.To.Type = obj.TYPE_MEM
				p.To.Reg = dstReg
				p.To.Offset = offset

				offset += 16
				rem -= 16
			}
		}
		// Generate all the remaining load and store pairs, starting with
		// as many 8 byte moves as possible, then 4, 2, 1.
		for rem > 0 {
			op, size := ppc.AMOVB, int64(1)
			switch {
			case rem >= 8:
				op, size = ppc.AMOVD, 8
			case rem >= 4:
				op, size = ppc.AMOVW, 4
			case rem >= 2:
				op, size = ppc.AMOVH, 2
			}
			// Load
			p := s.Prog(op)
			p.To.Type = obj.TYPE_REG
			p.To.Reg = ppc.REGTMP
			p.From.Type = obj.TYPE_MEM
			p.From.Reg = srcReg
			p.From.Offset = offset

			// Store
			p = s.Prog(op)
			p.From.Type = obj.TYPE_REG
			p.From.Reg = ppc.REGTMP
			p.To.Type = obj.TYPE_MEM
			p.To.Reg = dstReg
			p.To.Offset = offset
			rem -= size
			offset += size
		}

	case ssa.OpPPCCALLstatic:
		s.Call(v)

	case ssa.OpPPCCALLclosure, ssa.OpPPCCALLinter:
		p := s.Prog(ppc.AMOVD)
		p.From.Type = obj.TYPE_REG
		p.From.Reg = v.Args[0].Reg()
		p.To.Type = obj.TYPE_REG
		p.To.Reg = ppc.REG_LR

		if v.Args[0].Reg() != ppc.REG_R12 {
			v.Fatalf("Function address for %v should be in R12 %d but is in %d", v.LongString(), ppc.REG_R12, p.From.Reg)
		}

		pp := s.Call(v)
		pp.To.Reg = ppc.REG_LR

		if gc.Ctxt.Flag_shared {
			// When compiling Go into PIC, the function we just
			// called via pointer might have been implemented in
			// a separate module and so overwritten the TOC
			// pointer in R2; reload it.
			q := s.Prog(ppc.AMOVD)
			q.From.Type = obj.TYPE_MEM
			q.From.Offset = 24
			q.From.Reg = ppc.REGSP
			q.To.Type = obj.TYPE_REG
			q.To.Reg = ppc.REG_R2
		}

	case ssa.OpPPCLoweredWB:
		p := s.Prog(obj.ACALL)
		p.To.Type = obj.TYPE_MEM
		p.To.Name = obj.NAME_EXTERN
		p.To.Sym = v.Aux.(*obj.LSym)

	case ssa.OpPPCLoweredPanicBoundsA, ssa.OpPPCLoweredPanicBoundsB, ssa.OpPPCLoweredPanicBoundsC:
		p := s.Prog(obj.ACALL)
		p.To.Type = obj.TYPE_MEM
		p.To.Name = obj.NAME_EXTERN
		p.To.Sym = gc.BoundsCheckFunc[v.AuxInt]
		s.UseArgs(16) // space used in callee args area by assembly stubs

	case ssa.OpPPCLoweredNilCheck:
		if objabi.GOOS == "aix" {
			// CMP Rarg0, R0
			// BNE 2(PC)
			// STW R0, 0(R0)
			// NOP (so the BNE has somewhere to land)

			// CMP Rarg0, R0
			p := s.Prog(ppc.ACMP)
			p.From.Type = obj.TYPE_REG
			p.From.Reg = v.Args[0].Reg()
			p.To.Type = obj.TYPE_REG
			p.To.Reg = ppc.REG_R0

			// BNE 2(PC)
			p2 := s.Prog(ppc.ABNE)
			p2.To.Type = obj.TYPE_BRANCH

			// STW R0, 0(R0)
			// Write at 0 is forbidden and will trigger a SIGSEGV
			p = s.Prog(ppc.AMOVW)
			p.From.Type = obj.TYPE_REG
			p.From.Reg = ppc.REG_R0
			p.To.Type = obj.TYPE_MEM
			p.To.Reg = ppc.REG_R0

			// NOP (so the BNE has somewhere to land)
			nop := s.Prog(obj.ANOP)
			gc.Patch(p2, nop)

		} else {
			// Issue a load which will fault if arg is nil.
			p := s.Prog(ppc.AMOVBZ)
			p.From.Type = obj.TYPE_MEM
			p.From.Reg = v.Args[0].Reg()
			gc.AddAux(&p.From, v)
			p.To.Type = obj.TYPE_REG
			p.To.Reg = ppc.REGTMP
		}
		if logopt.Enabled() {
			logopt.LogOpt(v.Pos, "nilcheck", "genssa", v.Block.Func.Name)
		}
		if gc.Debug_checknil != 0 && v.Pos.Line() > 1 { // v.Pos.Line()==1 in generated wrappers
			gc.Warnl(v.Pos, "generated nil check")
		}

	// These should be resolved by rules and not make it here.
	case ssa.OpPPCEqual, ssa.OpPPCNotEqual, ssa.OpPPCLessThan, ssa.OpPPCFLessThan,
		ssa.OpPPCLessEqual, ssa.OpPPCGreaterThan, ssa.OpPPCFGreaterThan, ssa.OpPPCGreaterEqual,
		ssa.OpPPCFLessEqual, ssa.OpPPCFGreaterEqual:
		v.Fatalf("Pseudo-op should not make it to codegen: %s ###\n", v.LongString())
	case ssa.OpPPCInvertFlags:
		v.Fatalf("InvertFlags should never make it to codegen %v", v.LongString())
	case ssa.OpPPCFlagEQ, ssa.OpPPCFlagLT, ssa.OpPPCFlagGT, ssa.OpPPCFlagCarrySet, ssa.OpPPCFlagCarryClear:
		v.Fatalf("Flag* ops should never make it to codegen %v", v.LongString())
	case ssa.OpClobber:
		// TODO: implement for clobberdead experiment. Nop is ok for now.
	default:
		v.Fatalf("genValue not implemented: %s", v.LongString())
	}
}

var blockJump = [...]struct {
	asm, invasm     obj.As
	asmeq, invasmun bool
}{
	ssa.BlockPPCEQ: {ppc.ABEQ, ppc.ABNE, false, false},
	ssa.BlockPPCNE: {ppc.ABNE, ppc.ABEQ, false, false},

	ssa.BlockPPCLT: {ppc.ABLT, ppc.ABGE, false, false},
	ssa.BlockPPCGE: {ppc.ABGE, ppc.ABLT, false, false},
	ssa.BlockPPCLE: {ppc.ABLE, ppc.ABGT, false, false},
	ssa.BlockPPCGT: {ppc.ABGT, ppc.ABLE, false, false},

	// TODO: need to work FP comparisons into block jumps
	ssa.BlockPPCFLT: {ppc.ABLT, ppc.ABGE, false, false},
	ssa.BlockPPCFGE: {ppc.ABGT, ppc.ABLT, true, true}, // GE = GT or EQ; !GE = LT or UN
	ssa.BlockPPCFLE: {ppc.ABLT, ppc.ABGT, true, true}, // LE = LT or EQ; !LE = GT or UN
	ssa.BlockPPCFGT: {ppc.ABGT, ppc.ABLE, false, false},
}

func ssaGenBlock(s *gc.SSAGenState, b, next *ssa.Block) {
	switch b.Kind {
	case ssa.BlockDefer:
		// defer returns in R3:
		// 0 if we should continue executing
		// 1 if we should jump to deferreturn call
		p := s.Prog(ppc.ACMP)
		p.From.Type = obj.TYPE_REG
		p.From.Reg = ppc.REG_R3
		p.To.Type = obj.TYPE_REG
		p.To.Reg = ppc.REG_R0

		p = s.Prog(ppc.ABNE)
		p.To.Type = obj.TYPE_BRANCH
		s.Branches = append(s.Branches, gc.Branch{P: p, B: b.Succs[1].Block()})
		if b.Succs[0].Block() != next {
			p := s.Prog(obj.AJMP)
			p.To.Type = obj.TYPE_BRANCH
			s.Branches = append(s.Branches, gc.Branch{P: p, B: b.Succs[0].Block()})
		}

	case ssa.BlockPlain:
		if b.Succs[0].Block() != next {
			p := s.Prog(obj.AJMP)
			p.To.Type = obj.TYPE_BRANCH
			s.Branches = append(s.Branches, gc.Branch{P: p, B: b.Succs[0].Block()})
		}
	case ssa.BlockExit:
	case ssa.BlockRet:
		s.Prog(obj.ARET)
	case ssa.BlockRetJmp:
		p := s.Prog(obj.AJMP)
		p.To.Type = obj.TYPE_MEM
		p.To.Name = obj.NAME_EXTERN
		p.To.Sym = b.Aux.(*obj.LSym)

	case ssa.BlockPPCEQ, ssa.BlockPPCNE,
		ssa.BlockPPCLT, ssa.BlockPPCGE,
		ssa.BlockPPCLE, ssa.BlockPPCGT,
		ssa.BlockPPCFLT, ssa.BlockPPCFGE,
		ssa.BlockPPCFLE, ssa.BlockPPCFGT:
		jmp := blockJump[b.Kind]
		switch next {
		case b.Succs[0].Block():
			s.Br(jmp.invasm, b.Succs[1].Block())
			if jmp.invasmun {
				// TODO: The second branch is probably predict-not-taken since it is for FP unordered
				s.Br(ppc.ABVS, b.Succs[1].Block())
			}
		case b.Succs[1].Block():
			s.Br(jmp.asm, b.Succs[0].Block())
			if jmp.asmeq {
				s.Br(ppc.ABEQ, b.Succs[0].Block())
			}
		default:
			if b.Likely != ssa.BranchUnlikely {
				s.Br(jmp.asm, b.Succs[0].Block())
				if jmp.asmeq {
					s.Br(ppc.ABEQ, b.Succs[0].Block())
				}
				s.Br(obj.AJMP, b.Succs[1].Block())
			} else {
				s.Br(jmp.invasm, b.Succs[1].Block())
				if jmp.invasmun {
					// TODO: The second branch is probably predict-not-taken since it is for FP unordered
					s.Br(ppc.ABVS, b.Succs[1].Block())
				}
				s.Br(obj.AJMP, b.Succs[0].Block())
			}
		}
	default:
		b.Fatalf("branch not implemented: %s", b.LongString())
	}
}
