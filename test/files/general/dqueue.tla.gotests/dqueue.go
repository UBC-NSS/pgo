package dqueue

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
)

var _ = new(fmt.Stringer)  // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.TLAValue{} // same, for distsys

type Constants struct {
	BUFFER_SIZE   distsys.TLAValue
	NUM_CONSUMERS distsys.TLAValue
	PRODUCER      distsys.TLAValue
}

func NUM_NODES(constants Constants) distsys.TLAValue {
	return distsys.TLA_PlusSymbol(constants.NUM_CONSUMERS, distsys.NewTLANumber(1))
}

func AConsumer(ctx *distsys.MPCalContext, self distsys.TLAValue, constants Constants, net distsys.ArchetypeResourceHandle, proc distsys.ArchetypeResourceHandle) error {
	var err error
	// label tags
	const (
		cLabelTag = iota
		c1LabelTag
		c2LabelTag
		DoneLabelTag
	)
	programCounter := distsys.EnsureLocalArchetypeResource(ctx.ResourceEnsurerPositional(), distsys.NewTLANumber(cLabelTag))

	for {
		if err != nil {
			if err == distsys.CriticalSectionAborted {
				ctx.Abort()
				err = nil
			} else {
				return err
			}
		}
		labelTag, err := ctx.Read(programCounter, []distsys.TLAValue{})
		if err != nil {
			return err
		}
		switch labelTag.AsNumber() {
		case cLabelTag:
			if distsys.TLA_TRUE.AsBool() {
				err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(c1LabelTag))
				if err != nil {
					continue
				}
				err = ctx.Commit()
				if err != nil {
					continue
				}
			} else {
				err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(DoneLabelTag))
				if err != nil {
					continue
				}
				err = ctx.Commit()
				if err != nil {
					continue
				}
			}
			// no statements
		case c1LabelTag:
			err = ctx.Write(net, []distsys.TLAValue{constants.PRODUCER}, self)
			if err != nil {
				continue
			}
			err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(c2LabelTag))
			if err != nil {
				continue
			}
			err = ctx.Commit()
			if err != nil {
				continue
			}
		case c2LabelTag:
			var exprRead distsys.TLAValue
			exprRead, err = ctx.Read(net, []distsys.TLAValue{self})
			if err != nil {
				continue
			}
			err = ctx.Write(proc, []distsys.TLAValue{}, exprRead)
			if err != nil {
				continue
			}
			err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(cLabelTag))
			if err != nil {
				continue
			}
			err = ctx.Commit()
			if err != nil {
				continue
			}
		case DoneLabelTag:
			return nil
		default:
			return fmt.Errorf("invalid program counter %v", labelTag)
		}
	}
}
func AProducer(ctx *distsys.MPCalContext, self distsys.TLAValue, constants Constants, net0 distsys.ArchetypeResourceHandle, s distsys.ArchetypeResourceHandle) error {
	var err0 error
	// label tags
	const (
		pLabelTag = iota
		p1LabelTag
		p2LabelTag
		DoneLabelTag
	)
	programCounter0 := distsys.EnsureLocalArchetypeResource(ctx.ResourceEnsurerPositional(), distsys.NewTLANumber(pLabelTag))
	requester := distsys.EnsureLocalArchetypeResource(ctx.ResourceEnsurerPositional(), distsys.TLAValue{})
	_ = requester

	for {
		if err0 != nil {
			if err0 == distsys.CriticalSectionAborted {
				ctx.Abort()
				err0 = nil
			} else {
				return err0
			}
		}
		labelTag0, err0 := ctx.Read(programCounter0, []distsys.TLAValue{})
		if err0 != nil {
			return err0
		}
		switch labelTag0.AsNumber() {
		case pLabelTag:
			if distsys.TLA_TRUE.AsBool() {
				err0 = ctx.Write(programCounter0, []distsys.TLAValue{}, distsys.NewTLANumber(p1LabelTag))
				if err0 != nil {
					continue
				}
				err0 = ctx.Commit()
				if err0 != nil {
					continue
				}
			} else {
				err0 = ctx.Write(programCounter0, []distsys.TLAValue{}, distsys.NewTLANumber(DoneLabelTag))
				if err0 != nil {
					continue
				}
				err0 = ctx.Commit()
				if err0 != nil {
					continue
				}
			}
			// no statements
		case p1LabelTag:
			var exprRead0 distsys.TLAValue
			exprRead0, err0 = ctx.Read(net0, []distsys.TLAValue{self})
			if err0 != nil {
				continue
			}
			err0 = ctx.Write(requester, []distsys.TLAValue{}, exprRead0)
			if err0 != nil {
				continue
			}
			err0 = ctx.Write(programCounter0, []distsys.TLAValue{}, distsys.NewTLANumber(p2LabelTag))
			if err0 != nil {
				continue
			}
			err0 = ctx.Commit()
			if err0 != nil {
				continue
			}
		case p2LabelTag:
			var exprRead1 distsys.TLAValue
			exprRead1, err0 = ctx.Read(s, []distsys.TLAValue{})
			if err0 != nil {
				continue
			}
			var indexRead distsys.TLAValue
			indexRead, err0 = ctx.Read(requester, []distsys.TLAValue{})
			if err0 != nil {
				continue
			}
			err0 = ctx.Write(net0, []distsys.TLAValue{indexRead}, exprRead1)
			if err0 != nil {
				continue
			}
			err0 = ctx.Write(programCounter0, []distsys.TLAValue{}, distsys.NewTLANumber(pLabelTag))
			if err0 != nil {
				continue
			}
			err0 = ctx.Commit()
			if err0 != nil {
				continue
			}
		case DoneLabelTag:
			return nil
		default:
			return fmt.Errorf("invalid program counter %v", labelTag0)
		}
	}
}
