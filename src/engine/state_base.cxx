#include "state_base.h"
#include "state_class.h"

using namespace TR;

clock_t tr_begin_run = clock();


__attribute__((noreturn))
static void failure_exit() {
    throw Expt::IRfailureExit("valgrind error exit");
}

static void _vex_log_bytes(const HChar* bytes, SizeT nbytes) {
    std::cout << bytes;
}

static void IR_init(VexControl& vc) {
    static Bool TR_initdone = False;
    tr_begin_run = clock();
    if (!TR_initdone) {
        Func_Map_Init();
        LibVEX_Init(&failure_exit, &_vex_log_bytes, 0/*debuglevel*/, &vc);
        TR_initdone = True;
    }
}

tval StateBase::mk_int_const(UShort nbit) {
    std::unique_lock<std::mutex> lock(m_state_lock);
    auto res = m_z3_bv_const_n++;
    char buff[20];
#ifdef _MSC_VER
    sprintf_s(buff, sizeof(buff), "p_%d", res);
#else
    snprintf(buff, sizeof(buff), "p_%d", res);
#endif
    return tval(m_ctx, m_ctx.bv_const(buff, nbit), Z3_BV_SORT, nbit);
}

tval StateBase::mk_int_const(UShort n, UShort nbit) {
    char buff[20];
#ifdef _MSC_VER
    sprintf_s(buff, sizeof(buff), "p_%d", n);
#else
    snprintf(buff, sizeof(buff), "p_%d", n);
#endif
    return  tval(m_ctx, m_ctx.bv_const(buff, nbit), Z3_BV_SORT, nbit);
}

StateBase::operator std::string() const {
    std::string str;
    char hex[30];
    std::string strContent;


    str.append("\n#entry:");
    snprintf(hex, sizeof(hex), "%llx", (size_t)guest_start_ep);
    strContent.assign(hex);
    str.append(strContent);
    str.append(" end:");
    snprintf(hex, sizeof(hex), "%llx ", (size_t)guest_start);
    strContent.assign(hex);
    str.append(strContent);

    switch (m_status) {
    case NewState:str.append("NewState "); break;
    case Running:str.append("Running "); break;
    case Fork:str.append("Fork "); break;
    case Death:str.append("Death "); break;
    case Exit:str.append("Exit "); break;
    default:
        snprintf(hex, sizeof(hex), "%d ", m_status);
        strContent.assign(hex);
        str.append(strContent); break;
    }

    str.append(" #child{\n");
    if (branch.empty()) {
        switch (m_status) {
        case NewState:str.append("NewState "); break;
        case Running:str.append("Running "); break;
        case Fork:str.append("Fork "); break;
        case Death:str.append("Death "); break;
        case Exit:str.append("Exit "); break;
        default:
            snprintf(hex, sizeof(hex), "status:%d ", m_status);
            strContent.assign(hex);
            str.append(strContent); break;
        }
        snprintf(hex, sizeof(hex), "%llx    \n}\n ", (size_t)guest_start);
        strContent.assign(hex);
        str.append(strContent);
        return str;
    }
    else {
        for (auto state : branch) {
            std::string child = *state;
            str.append(replace(child.c_str(), "\n", "\n   >"));
        }
    }
    str.append("\n}\n");
    return str;
}



void StateBase::read_mem_dump(const char* filename)
{
    struct memdump {
        unsigned long long nameoffset;
        unsigned long long address;
        unsigned long long length;
        unsigned long long dataoffset;
    }buf;
    if (!filename) return;
    std::ifstream infile;
    infile.open(filename, std::ios::binary);
    if (!infile.is_open()) {
        if (filename[0] == 0) { return; }
        std::cerr << filename << "not exit/n" << std::endl; return;
    }
    unsigned long long length, err, name_start_offset, name_end_offset, need_write_size = 0, write_count = 0;
    infile.seekg(0, std::ios::beg);
    infile.read((char*)&length, 8);
    infile.seekg(24, std::ios::beg);
    name_start_offset = length;
    infile.read((char*)&name_end_offset, 8);
    length /= 32;
    char* name_buff = (char*)malloc(name_end_offset - name_start_offset);
    infile.seekg(name_start_offset, std::ios::beg);
    infile.read(name_buff, name_end_offset - name_start_offset);
    infile.seekg(0, std::ios::beg);
    char* name;
    printf("Initializing Virtual Memory\n/------------------------------+--------------------+--------------------+------------\\\n");
    printf("|              SN              |         VA         |         FOA        |     LEN    |\n");
    printf("+------------------------------+--------------------+--------------------+------------+\n");
    
    clock_t beginCount = clock();

    for (unsigned int segnum = 0; segnum < length; segnum++) {
        infile.read((char*)&buf, 32);
        char* data = (char*)malloc(buf.length);
        std::streampos fp = infile.tellg();
        infile.seekg(buf.dataoffset, std::ios::beg);
        infile.read(data, buf.length);
        name = &name_buff[buf.nameoffset - name_start_offset];
        if (GET8(name) == 0x7265747369676572) {
#if 0
            printf("name:%18s address:%016llx data offset:%010llx length:%010llx\n", name, buf.address, buf.dataoffset, buf.length);
#endif
            regs.Ist_Put(buf.address, data, buf.length);
        }
        else {
            printf("| %-28s |  %16llx  |  %16llx  | %10llx |\n", name, buf.address, buf.dataoffset, buf.length);
            if (err = mem().membase(buf.address, buf.length))
                printf("warning %s had maped before length: %llx\n", name, err);
            need_write_size += buf.length;
            write_count += membase().write_bytes(buf.address, buf.length, (unsigned char*)data);
        }
        infile.seekg(fp);
        free(data);
    }
    printf("\\-------------------------------------------------------------------------------------/\n");

    clock_t closeCount = clock();
    printf(
        "Spend time in:   %16d s.\n"
        "Need to write    %16lf MByte.\n"
        "Actually written %16lf MByte\n", closeCount - beginCount, ((double)need_write_size) / 0x100000, ((double)write_count) / 0x100000);
    free(name_buff);
    infile.close();
}

TR::StateBase::StateBase(TR::vctx_base& vctx_base, HWord gse, Bool _need_record)
    :m_ctx(), m_vex_info(vctx_base),
    guest_start_ep(/*oep*/0),
    guest_start(/*oep*/0),
    m_need_record(_need_record),
    m_z3_bv_const_n(0),
    m_delta(0),
    m_status(NewState),
    m_jump_kd(Ijk_Boring),
    m_InvokStack(),
    solv(m_ctx),
    regs(m_ctx, _need_record),
    branch(*this)
{

    vctx_base.set_top_state(this);
    VexControl vc;
    LibVEX_default_VexControl(&vc);
    vc.iropt_verbosity = 0;
    vc.iropt_level = info().giropt_level();
    #warning "whate is iropt_unroll_thresh"
        vc.iropt_unroll_thresh = 0;
    vc.guest_max_insns = info().gmax_insns();
    //vc.guest_chase_thresh = 0;   
    vc.guest_chase = True; //²»Ðí×·¸Ï
    vc.iropt_register_updates_default = info().gRegisterUpdates();
    IR_init(vc);

    read_mem_dump(info().gbin());
    if (gse)
        guest_start_ep = gse;
    else {
        guest_start_ep = regs.get<HWord>(info().gRegsIpOffset()).tor();
    }
    guest_start = guest_start_ep;


    /*auto _TraceIrAddrress = info().doc_debug->FirstChildElement("TraceIrAddrress");
    if (_TraceIrAddrress) {
        for (auto ta = _TraceIrAddrress->FirstChildElement(); ta; ta = ta->NextSiblingElement()) {
            ULong addr; TRControlFlags flag;
            sscanf(ta->Attribute("addr"), "%llx", &addr);
            sscanf(ta->Attribute("cflag"), "%llx", &flag);
            vctx.hook_add(addr, nullptr, flag);
        }
    }*/

}

TR::StateBase::StateBase(StateBase& father, HWord gse)
    : m_ctx(), m_vex_info(father.m_vex_info),
    guest_start_ep(gse),
    guest_start(guest_start_ep),
    m_need_record(father.m_need_record),
    m_z3_bv_const_n(father.m_z3_bv_const_n),
    m_delta(0),
    m_status(NewState),
    m_jump_kd(Ijk_Boring),
    m_InvokStack(father.m_InvokStack),
    solv(m_ctx, father.solv, z3::solver::translate{}),
    regs(father.regs, m_ctx, father.m_need_record),
    branch(*this, father.branch)
{};


