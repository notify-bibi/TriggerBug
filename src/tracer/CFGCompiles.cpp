
#include "instopt/tracer/CFGTracer.h"
#include "instopt/engine/tr_kernel.h"
#include "vexllvm/genllvm.h"
#include "vexllvm/Sugar.h"
#include "vexllvm/vexsb.h"
#include "vexllvm/vexstmt.h"
#include "vexllvm/vexexpr.h"
#include "vexllvm/vexcpustate.h"
#include "vexllvm/vexhelpers.h"



using namespace llvm;
class BL {
public:
    BasicBlock* BB;
    const BlockView* BV;
    Value* ret;

    BL() {}
    BL(BasicBlock* BB, const BlockView* BV, Value* ret)
        : BB(BB), BV(BV), ret(ret) {}
    BL(const BL& B) : BB(B.BB), BV(B.BV), ret(B.ret) {}
    void operator=(const BL& B) {
        BB = B.BB;
        BV = B.BV;
        ret = B.ret;
    }
};

class FlatCFG {
    llvm::LLVMContext& ctx;
    std::unique_ptr<llvm::IRBuilder<>> builder;
    llvm::Module& mod;
    llvm::FunctionType* funcTy = nullptr;
    llvm::Function* cur_f = nullptr;
    llvm::BasicBlock* entry_bb = nullptr;
    llvm::BasicBlock* unhandle_bb = nullptr;
    llvm::Value* cur_guest_ctx = nullptr;
    Value* pRet;
    std::unordered_map<const BlockView*, llvm::Function*> m_collect;

public:
    FlatCFG(llvm::LLVMContext& ctx, llvm::Module& mod) : ctx(ctx), mod(mod) {
        builder = std::make_unique<IRBuilder<>>(ctx);
        mkFuncTy(64);
    }

    void mkFuncTy(unsigned N)
    {
        std::vector<Type*>	f_args;
        std::vector<Type*>	types;

        // StructType* guestCtxTy = StructType::create(ctx, types, "guestCtxTy");
        Type* guestCtxTy = GenLLVM::getGenLLVM()->getGuestTy();
        f_args.push_back(PointerType::get(guestCtxTy, 0));

        funcTy = FunctionType::get(builder->getIntNTy(N), f_args, false);

    }

    void beginBB(const char* name)
    {
        assert(entry_bb == NULL && "nested beginBB");
        cur_f = Function::Create(
            funcTy,
            Function::ExternalLinkage,
            name,
            mod);

        // XXX: marking the regctx as noalias could mess up any instrumentation
        // that wants to modify registers, but I'm not sure if that would ever
        // be a thing I'd want to do
        cur_f->arg_begin()->addAttr(Attribute::AttrKind::NoAlias);

        entry_bb = BasicBlock::Create(ctx, "entry", cur_f);
        builder->SetInsertPoint(entry_bb);

        Function::arg_iterator arg = cur_f->arg_begin();

        //arg->addAttr(Attributes(Attributes::NoAlias));
        cur_guest_ctx = &(*arg);

        auto i64ty = Type::getInt64Ty(ctx);
        pRet = builder->CreateAlloca(i64ty, nullptr, "unhandleRet");

        unhandle_bb = BasicBlock::Create(getGlobalContext(), "unhandle",
            entry_bb->getParent());

#if 0
        Value* Lctx = builder->CreateAlloca(getGuestTy(), nullptr);
        Value* Tmp = builder->CreateLoad(cur_guest_ctx);
        builder->CreateStore(Tmp, Lctx);
        cur_guest_ctx = Lctx;
#endif


        arg++;

    }

    void endBB(Value* retVal) {
        builder->CreateRet(retVal);
    }

    llvm::Function* emitIRSB(const BlockView& basic_irsb_chunk) {
        auto f = m_collect.find(&basic_irsb_chunk);
        if (f != m_collect.end()) {
            return f->second;
        };
        // ---------------------------------------
        irsb_chunk irsb = basic_irsb_chunk.get_irsb_chunk();
        VexArch arch = irsb->get_arch();
        VexHelpers::getVexHelpers()->loadDefaultModules(arch);
        GenLLVM::getGenLLVM()->mkFuncTy(
            basic_irsb_chunk.get_irsb_chunk()->get_numBits());
        guest_ptr guest_addr;
        VexSB sb(guest_addr, irsb->get_irsb());
        std::stringstream st;
        st << "bb_" << std::hex
            << basic_irsb_chunk.get_irsb_chunk()->get_bb_base() << "_" << std::dec
            << basic_irsb_chunk.get_irsb_chunk()->get_bb_base();
        llvm::Function* F = sb.emit(st.str().c_str());
        // ---------------------------------------
        return F;
    }

    Value* mkGuard(guest_ptr p, unsigned numBits, Value* L) {
        Value* ptr = ConstantInt::get(getGlobalContext(), APInt(numBits, p));
        return builder->CreateICmpEQ(L, ptr);
    }


    Value* SaveRet(Value* V, bool retImm) {
        Value* ret;
        unsigned sz = V->getType()->getIntegerBitWidth();
        if (sz != 64) {
            ret = builder->CreateZExt(V, IntegerType::get(ctx, 64));
        }
        else {
            ret = V;
        }
        if (retImm) {
            endBB(ret);
            return ret;
        }
        else {
            builder->CreateStore(ret, pRet);
            builder->CreateBr(unhandle_bb);
            return ret;
        }
    }



    void emitNext(Value* v_cmp, const BlockView* next, BasicBlock* bb) {
        BasicBlock* bb_then, * bb_else, * bb_origin;

        bb_origin = builder->GetInsertBlock();
        bb_then = BasicBlock::Create(getGlobalContext(), "if_then",
            bb_origin->getParent());
        bb_else = BasicBlock::Create(getGlobalContext(), "if_else",
            bb_origin->getParent());

        /* evaluate guard condition */
        builder->SetInsertPoint(bb_origin);
        builder->CreateCondBr(v_cmp, bb_then, bb_else);

        /* guard condition return, leave this place */
        /* XXX for calls we're going to need some more info */
        builder->SetInsertPoint(bb_then);

        builder->CreateBr(bb);


        /* continue on */
        builder->SetInsertPoint(bb_else);
    }


    void functionFinder(GraphView GV, const BlockView& entry) {
        




    }

    void compile(GraphView GV, const BlockView& entry, bool retImm = true) {
        beginBB("A_VMP");

        std::unordered_map<Addr, BL> map;

        for (auto it = GV.get_blocks().begin(); it != GV.get_blocks().end();
            it++) {
            const BlockView* curr = &it->second;
            llvm::Function* F = emitIRSB(*curr);
            std::stringstream st;
            st << "bb_" << std::hex << curr->get_irsb_chunk()->get_bb_base() << "_"
                << std::dec << curr->get_irsb_chunk()->get_bb_base();

            BasicBlock* bb_then = BasicBlock::Create(getGlobalContext(), st.str().c_str(), entry_bb->getParent());
            builder->SetInsertPoint(bb_then);
            Value* Ret = builder->CreateCall(F, cur_guest_ctx);
            map[curr->get_irsb_chunk()->get_bb_base()] = BL(bb_then, curr, Ret);
        }


        for (auto it = GV.get_blocks().begin(); it != GV.get_blocks().end();
            it++) {
            const BlockView* curr = &it->second;
            auto& B = map[curr->get_irsb_chunk()->get_bb_base()];
            builder->SetInsertPoint(B.BB);
            for (auto Nit = curr->get_nexts().begin();
                Nit != curr->get_nexts().end(); Nit++) {
                BlockView* Next = *Nit;
                auto& NB = map[Next->get_irsb_chunk()->get_bb_base()];
                Value* cmp =
                    mkGuard((guest_ptr)Next->get_irsb_chunk()->get_bb_base(),
                        curr->get_irsb_chunk()->get_numBits(), B.ret);

                emitNext(cmp, NB.BV, NB.BB);
            }

            SaveRet(B.ret, retImm);
        }

        builder->SetInsertPoint(entry_bb);
        auto& EntryBB = map[entry.get_irsb_chunk()->get_bb_base()];
        BranchInst* Binst = builder->CreateBr(EntryBB.BB);
        // Value *Ret = lift(&entry);
        // endBB(Ret);

        builder->SetInsertPoint(unhandle_bb);
        Value* Ret = builder->CreateLoad(pRet, "ret");
        endBB(Ret);

    };
};




void compile(GraphView& gv, BlockView& basic_irsb_chunk)
{
    auto sh = StateHelper::get(VexArchAMD64);
    GenLLVM::getGenLLVM() = std::make_unique<GenLLVM>(*sh);
    VexHelpers::getVexHelpers() = VexHelpers::create(VexArchX86);


    FlatCFG FC(GenLLVM::getGenLLVM()->getContext(), GenLLVM::getGenLLVM()->getModule());
    FC.compile(gv, basic_irsb_chunk);
}