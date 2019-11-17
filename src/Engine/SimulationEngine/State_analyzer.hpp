#include "State_class.hpp"



class Block {
    ADDR m_front;
    ADDR m_end;
    std::vector<Block*> m_out;
    std::vector<Block*> m_in;
public:
    inline Block(ADDR front = 0, ADDR end = 0) :
        m_front(m_front),
        m_end(end){}
    inline void setfront(ADDR front) { m_front = front; }
    inline void setEnd(ADDR end) { m_end = end; }
    inline void push_in(Block& in) { m_in.emplace_back(&in); }
    inline void push_out(Block& out) { m_out.emplace_back(&out); }

private:

};

class IRT {
    UInt irTempSize;
    IRExpr** irTemp;
public:
    IRT() {
        irTempSize = 10;
        irTemp = (IRExpr**)malloc(sizeof(IRExpr*) * irTempSize);
    }

    IRExpr*& operator [](UInt idx) {
        if (idx >= irTempSize) {
            if (idx < 2 * irTempSize) {
                IRExpr** newtmp = (IRExpr**)malloc(sizeof(IRExpr*) * 2 * irTempSize);
                for (int i = 0; i < irTempSize; i++) {
                    newtmp[i] = irTemp[i];
                }
                irTempSize = 2 * irTempSize;
                irTemp = newtmp;
            }
            else {
                IRExpr** newtmp = (IRExpr**)malloc(sizeof(IRExpr*) * (idx + 1));
                for (int i = 0; i < irTempSize; i++) {
                    newtmp[i] = irTemp[i];
                }
                irTempSize = idx + 1;
                irTemp = newtmp;
            }
        }
        return irTemp[idx];
    }
};




class WriteMap {
    IRSB const* irsb;
    struct Bms {
        IRExpr* address;
        IRExpr* mem;
        UShort nb;
    };
    std::vector<Bms> unit;
public:
    WriteMap(IRSB const*bb):
        irsb(bb)
    {
        unit.reserve(10);
    }

    void Ist_Store(IRExpr *address, IRExpr* data) {
        IRType ty = typeOfIRExpr(irsb->tyenv, data);
        UShort dnb = sizeofIRType(ty);
        unit.emplace_back(Bms{ address, data, dnb });
    }
};

class GraphView{
    State& m_state;
    context& m_ctx;
    Register<REGISTER_LEN>& regs;
    MEM& mem;
    UShort t_index;
    ADDR guest_start_ep;
    ADDR guest_start;
    bool is_dynamic_block;
    Pap pap; 
    Long delta;
    IRT irTemp;
public:
    GraphView(State& state):
        m_state(state),
        m_ctx(state),
        regs(state.regs),
        mem(state.mem),
        t_index(0),
        guest_start_ep(state.guest_start_ep),
        guest_start(state.guest_start),
        pap(state.pap),
        delta(0),
        irTemp()
    {
    }
    IRSB* BB2IR();
    inline IRExpr* tIRExpr(IRExpr* e);
    void analyze(ADDR block_oep);
};



class StateAnalyzer {
    State& m_state;
public:
    StateAnalyzer(State& state) :
        m_state(state)
    {
    }

    void analyze(State &s) {
        GraphView gv(s);
        gv.analyze(s.get_start_of_block());
    }

    void Run();

};