

bool creakme() {
    ctx32 v(VexArchX86, "C:\\Users\\bibi\\Desktop\\TriggerBug\\PythonFrontEnd\\examples\\SCTF-creakMe\\creakme.exe.dump");
    v.getFlags();



    SP::X86 state(v, 0, True);

    state.start();
    
}