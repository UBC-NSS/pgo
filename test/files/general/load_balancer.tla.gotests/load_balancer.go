package loadbalancer

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
)

var _ = new(fmt.Stringer)  // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.TLAValue{} // same, for distsys

type Constants struct {
	BUFFER_SIZE    distsys.TLAValue
	LoadBalancerId distsys.TLAValue
	NUM_SERVERS    distsys.TLAValue
	NUM_CLIENTS    distsys.TLAValue
	GET_PAGE       distsys.TLAValue
	WEB_PAGE       distsys.TLAValue
}

func NUM_NODES(constants Constants) distsys.TLAValue {
	return distsys.TLA_PlusSymbol(distsys.TLA_PlusSymbol(constants.NUM_CLIENTS, constants.NUM_SERVERS), distsys.NewTLANumber(1))
}

func ALoadBalancer(ctx *distsys.MPCalContext, self distsys.TLAValue, constants Constants, mailboxes distsys.ArchetypeResourceHandle) error {
	var err error
	// label tags
	const (
		mainLabelTag = iota
		rcvMsgLabelTag
		sendServerLabelTag
		DoneLabelTag
	)
	programCounter := distsys.EnsureLocalArchetypeResource(ctx.ResourceEnsurerPositional(), distsys.NewTLANumber(mainLabelTag))
	msg := distsys.EnsureLocalArchetypeResource(ctx.ResourceEnsurerPositional(), distsys.TLAValue{})
	_ = msg
	next := distsys.EnsureLocalArchetypeResource(ctx.ResourceEnsurerPositional(), distsys.NewTLANumber(0))
	_ = next

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
		case mainLabelTag:
			if distsys.TLA_TRUE.AsBool() {
				err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(rcvMsgLabelTag))
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
		case rcvMsgLabelTag:
			var exprRead distsys.TLAValue
			exprRead, err = ctx.Read(mailboxes, []distsys.TLAValue{constants.LoadBalancerId})
			if err != nil {
				continue
			}
			err = ctx.Write(msg, []distsys.TLAValue{}, exprRead)
			if err != nil {
				continue
			}
			var condition distsys.TLAValue
			condition, err = ctx.Read(msg, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			if !distsys.TLA_EqualsSymbol(condition.ApplyFunction(distsys.NewTLAString("message_type")), constants.GET_PAGE).AsBool() {
				err = fmt.Errorf("%w: ((msg).message_type) = (GET_PAGE)", distsys.AssertionFailed)
				continue
			}
			err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(sendServerLabelTag))
			if err != nil {
				continue
			}
			err = ctx.Commit()
			if err != nil {
				continue
			}
		case sendServerLabelTag:
			var exprRead0 distsys.TLAValue
			exprRead0, err = ctx.Read(next, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			err = ctx.Write(next, []distsys.TLAValue{}, distsys.TLA_PlusSymbol(distsys.TLA_PercentSymbol(exprRead0, constants.NUM_SERVERS), distsys.NewTLANumber(1)))
			if err != nil {
				continue
			}
			var exprRead1 distsys.TLAValue
			exprRead1, err = ctx.Read(next, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			var exprRead2 distsys.TLAValue
			exprRead2, err = ctx.Read(msg, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			var exprRead3 distsys.TLAValue
			exprRead3, err = ctx.Read(msg, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			var indexRead distsys.TLAValue
			indexRead, err = ctx.Read(next, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			err = ctx.Write(mailboxes, []distsys.TLAValue{indexRead}, distsys.NewTLARecord([]distsys.TLARecordField{
				{distsys.NewTLAString("message_id"), exprRead1},
				{distsys.NewTLAString("client_id"), exprRead2.ApplyFunction(distsys.NewTLAString("client_id"))},
				{distsys.NewTLAString("path"), exprRead3.ApplyFunction(distsys.NewTLAString("path"))},
			}))
			if err != nil {
				continue
			}
			err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(mainLabelTag))
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
func AServer(ctx *distsys.MPCalContext, self distsys.TLAValue, constants Constants, mailboxes0 distsys.ArchetypeResourceHandle, file_system distsys.ArchetypeResourceHandle) error {
	var err0 error
	// label tags
	const (
		serverLoopLabelTag = iota
		rcvReqLabelTag
		sendPageLabelTag
		DoneLabelTag
	)
	programCounter0 := distsys.EnsureLocalArchetypeResource(ctx.ResourceEnsurerPositional(), distsys.NewTLANumber(serverLoopLabelTag))
	msg0 := distsys.EnsureLocalArchetypeResource(ctx.ResourceEnsurerPositional(), distsys.TLAValue{})
	_ = msg0

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
		case serverLoopLabelTag:
			if distsys.TLA_TRUE.AsBool() {
				err0 = ctx.Write(programCounter0, []distsys.TLAValue{}, distsys.NewTLANumber(rcvReqLabelTag))
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
		case rcvReqLabelTag:
			var exprRead4 distsys.TLAValue
			exprRead4, err0 = ctx.Read(mailboxes0, []distsys.TLAValue{self})
			if err0 != nil {
				continue
			}
			err0 = ctx.Write(msg0, []distsys.TLAValue{}, exprRead4)
			if err0 != nil {
				continue
			}
			err0 = ctx.Write(programCounter0, []distsys.TLAValue{}, distsys.NewTLANumber(sendPageLabelTag))
			if err0 != nil {
				continue
			}
			err0 = ctx.Commit()
			if err0 != nil {
				continue
			}
		case sendPageLabelTag:
			var exprRead5 distsys.TLAValue
			exprRead5, err0 = ctx.Read(msg0, []distsys.TLAValue{})
			if err0 != nil {
				continue
			}
			var exprRead6 distsys.TLAValue
			exprRead6, err0 = ctx.Read(file_system, []distsys.TLAValue{exprRead5.ApplyFunction(distsys.NewTLAString("path"))})
			if err0 != nil {
				continue
			}
			var indexRead0 distsys.TLAValue
			indexRead0, err0 = ctx.Read(msg0, []distsys.TLAValue{})
			if err0 != nil {
				continue
			}
			err0 = ctx.Write(mailboxes0, []distsys.TLAValue{indexRead0.ApplyFunction(distsys.NewTLAString("client_id"))}, exprRead6)
			if err0 != nil {
				continue
			}
			err0 = ctx.Write(programCounter0, []distsys.TLAValue{}, distsys.NewTLANumber(serverLoopLabelTag))
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
func AClient(ctx *distsys.MPCalContext, self distsys.TLAValue, constants Constants, mailboxes1 distsys.ArchetypeResourceHandle, instream distsys.ArchetypeResourceHandle, outstream distsys.ArchetypeResourceHandle) error {
	var err1 error
	// label tags
	const (
		clientLoopLabelTag = iota
		clientRequestLabelTag
		clientReceiveLabelTag
		DoneLabelTag
	)
	programCounter1 := distsys.EnsureLocalArchetypeResource(ctx.ResourceEnsurerPositional(), distsys.NewTLANumber(clientLoopLabelTag))
	req := distsys.EnsureLocalArchetypeResource(ctx.ResourceEnsurerPositional(), distsys.TLAValue{})
	_ = req
	resp := distsys.EnsureLocalArchetypeResource(ctx.ResourceEnsurerPositional(), distsys.TLAValue{})
	_ = resp

	for {
		if err1 != nil {
			if err1 == distsys.CriticalSectionAborted {
				ctx.Abort()
				err1 = nil
			} else {
				return err1
			}
		}
		labelTag1, err1 := ctx.Read(programCounter1, []distsys.TLAValue{})
		if err1 != nil {
			return err1
		}
		switch labelTag1.AsNumber() {
		case clientLoopLabelTag:
			if distsys.TLA_TRUE.AsBool() {
				err1 = ctx.Write(programCounter1, []distsys.TLAValue{}, distsys.NewTLANumber(clientRequestLabelTag))
				if err1 != nil {
					continue
				}
				err1 = ctx.Commit()
				if err1 != nil {
					continue
				}
			} else {
				err1 = ctx.Write(programCounter1, []distsys.TLAValue{}, distsys.NewTLANumber(DoneLabelTag))
				if err1 != nil {
					continue
				}
				err1 = ctx.Commit()
				if err1 != nil {
					continue
				}
			}
			// no statements
		case clientRequestLabelTag:
			var exprRead7 distsys.TLAValue
			exprRead7, err1 = ctx.Read(instream, []distsys.TLAValue{})
			if err1 != nil {
				continue
			}
			err1 = ctx.Write(req, []distsys.TLAValue{}, distsys.NewTLARecord([]distsys.TLARecordField{
				{distsys.NewTLAString("message_type"), constants.GET_PAGE},
				{distsys.NewTLAString("client_id"), self},
				{distsys.NewTLAString("path"), exprRead7},
			}))
			if err1 != nil {
				continue
			}
			var exprRead8 distsys.TLAValue
			exprRead8, err1 = ctx.Read(req, []distsys.TLAValue{})
			if err1 != nil {
				continue
			}
			err1 = ctx.Write(mailboxes1, []distsys.TLAValue{constants.LoadBalancerId}, exprRead8)
			if err1 != nil {
				continue
			}
			err1 = ctx.Write(programCounter1, []distsys.TLAValue{}, distsys.NewTLANumber(clientReceiveLabelTag))
			if err1 != nil {
				continue
			}
			err1 = ctx.Commit()
			if err1 != nil {
				continue
			}
		case clientReceiveLabelTag:
			var exprRead9 distsys.TLAValue
			exprRead9, err1 = ctx.Read(mailboxes1, []distsys.TLAValue{self})
			if err1 != nil {
				continue
			}
			err1 = ctx.Write(resp, []distsys.TLAValue{}, exprRead9)
			if err1 != nil {
				continue
			}
			var exprRead10 distsys.TLAValue
			exprRead10, err1 = ctx.Read(resp, []distsys.TLAValue{})
			if err1 != nil {
				continue
			}
			err1 = ctx.Write(outstream, []distsys.TLAValue{}, exprRead10)
			if err1 != nil {
				continue
			}
			err1 = ctx.Write(programCounter1, []distsys.TLAValue{}, distsys.NewTLANumber(clientLoopLabelTag))
			if err1 != nil {
				continue
			}
			err1 = ctx.Commit()
			if err1 != nil {
				continue
			}
		case DoneLabelTag:
			return nil
		default:
			return fmt.Errorf("invalid program counter %v", labelTag1)
		}
	}
}
