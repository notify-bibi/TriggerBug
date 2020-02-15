
int test_cmpress() {
    SP::AMD64 state("C:\\Users\\bibi\\Desktop\\TriggerBug\\PythonFrontEnd\\examples\\xctf-asong\\TriggerBug Engine\\asong.xml", 0, True);
    
    for (int i = 0; i < 4; i++) {
        SP::AMD64* s = (SP::AMD64*)(state.ForkState(20));
        Vns f1 = s->m_ctx.bv_const("a1", 8);
        Vns f2 = s->m_ctx.bv_const("a2", 8);
        s->solv.add_assert(f1 > i);
        s->solv.add_assert(f2 < i);
        s->mem.Ist_Store(0x602080, 1000+i);
        s->mem.Ist_Store(0x602088, 1000 + i);
        if(i==3)
            s->set_status(Death);
    }
    std::cout << state << std::endl;
    for (int i = 4; i < 5; i++) {
        SP::AMD64* s = (SP::AMD64*)(state.ForkState(32));
        Vns f1 = s->m_ctx.bv_const("aj", 8);
        Vns f2 = s->m_ctx.bv_const("ak", 8);
        s->solv.add_assert(f1 > i);
        s->solv.add_assert(f2 < i);
        s->set_status((State_Tag)88);
    }

    std::cout << state << std::endl;
    UInt i = 0;
    for (auto s : state.branch) {
        i += 1;
        if (i <= 3) { continue; }
        SP::AMD64* s2 = (SP::AMD64*)(s->ForkState(20));
        s->set_status(Fork);
        Vns f = s2->m_ctx.bv_const("b", 8);
        s2->solv.add_assert(f > i);
        s2->mem.Ist_Store(0x602080, 100 + i);
        s2->mem.Ist_Store(0x602081, 100ull + i+(1ull<<63));
        if (i <= 4)
            continue;
        s2->m_InvokStack.push(787, 87);
    }


    std::cout << state << std::endl;


    cmpr::Context64 c = state.cmprContext(20, NewState);
    c.add_avoid(Death);
    c.add_avoid((State_Tag)88);

    state.compress(c);
    std::cout << state << std::endl;
}