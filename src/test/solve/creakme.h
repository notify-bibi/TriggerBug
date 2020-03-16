
State_Tag hoo(State<Addr32> &s) {

    printf("hjkhjk");
    return Running;
}



bool creakme() {
    ctx32 v(VexArchX86, "C:\\Users\\bibi\\Desktop\\TriggerBug\\PythonFrontEnd\\examples\\SCTF-creakMe\\creakme.exe.dump");
    v.set_system(windows);
    v.setFlag(CF_traceJmp);
    v.setFlag(CF_ppStmts);

    SP::X86 state(v, 0, True);
    state.hook_add(0x4023EF, hoo);



    state.start();
    
}