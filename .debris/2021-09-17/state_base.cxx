
#include "instopt/engine/state_base.h"
#include "instopt/engine/z3_target_call/z3_target_call.h"

using namespace TR;



VexGuestState* TR::StateBase::get_regs_maps()
{
    return reinterpret_cast<VexGuestState*>(&regs.regs_bytes);
}

ULong TR::StateBase::get_cpu_sp() {
    ULong r = regs.get<ULong>(vinfo().gRegsSpOffset()).tor();
    if (vinfo().is_mode_32()) r &= 0xffffffff;
    return r;
}

sv::tval StateBase::mk_int_const(UShort nbit) {
    auto res = m_z3_bv_const_n++;
    char buff[20];
#ifdef _MSC_VER
    sprintf_s(buff, sizeof(buff), "p_%d", res);
#else
    snprintf(buff, sizeof(buff), "p_%d", res);
#endif
    return sv::tval(m_ctx, m_ctx.bv_const(buff, nbit), Z3_BV_SORT, nbit);
}

sv::tval StateBase::mk_int_const(UShort n, UShort nbit) {
    char buff[20];
#ifdef _MSC_VER
    sprintf_s(buff, sizeof(buff), "p_%d", n);
#else
    snprintf(buff, sizeof(buff), "p_%d", n);
#endif
    return  sv::tval(m_ctx, m_ctx.bv_const(buff, nbit), Z3_BV_SORT, nbit);
}

std::string replace(const char* pszSrc, const char* pszOld, const char* pszNew)
{
    std::string strContent, strTemp;
    strContent.assign(pszSrc);
    std::string::size_type nPos = 0;
    while (true)
    {
        nPos = strContent.find(pszOld, nPos);
        if (nPos == std::string::npos)
        {
            break;
        }
        strTemp = strContent.substr(nPos + strlen(pszOld), strContent.length());
        strContent.replace(nPos, strContent.length(), pszNew);
        strContent.append(strTemp);
        nPos += strlen(pszNew) - strlen(pszOld) + 1;
    }
    return strContent;
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
        spdlog::critical("{} not exit/n", filename);
        throw Expt::IRfailureExit("not exist");
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
    spdlog::info("Initializing Virtual Memory"); 
    spdlog::info("/------------------------------+--------------------+--------------------+------------\\");
    spdlog::info("|              SN              |         VA         |         FOA        |     LEN    |");
    spdlog::info("+------------------------------+--------------------+--------------------+------------+");
    
    clock_t beginCount = clock();

    for (unsigned int segnum = 0; segnum < length; segnum++) {
        infile.read((char*)&buf, 32);
        char* data = (char*)malloc(buf.length+32);
        std::streampos fp = infile.tellg();
        infile.seekg(buf.dataoffset, std::ios::beg);
        infile.read(data, buf.length);
        name = &name_buff[buf.nameoffset - name_start_offset];
        if (GET8(name) == 0x7265747369676572) {
#if 0
            spdlog::info("name:%18s address:%016llx data offset:%010llx length:%010llx", name, buf.address, buf.dataoffset, buf.length);
#endif
            regs.Ist_Put(buf.address, data, buf.length);
    }
        else {
            spdlog::info("| {:28s} |  {:16x}  |  {:16x}  | {:10x} |", name, buf.address, buf.dataoffset, buf.length);
            if (err = mem.map(buf.address, buf.length))
                spdlog::info("warning %s had maped before length: %llx", name, err);
            need_write_size += buf.length;
            write_count += mem.write_bytes(buf.address, buf.length, (unsigned char*)data);
        }
        infile.seekg(fp);
        free(data);
}
    spdlog::info("\\-------------------------------------------------------------------------------------/");

    clock_t closeCount = clock();
    spdlog::info("Spend time in:   {:16d} ms.", closeCount - beginCount);
    spdlog::info("Need to write    {} MByte.", ((double)need_write_size) / 0x100000);
    spdlog::info("Actually written {} MByte.", ((double)write_count) / 0x100000);
    free(name_buff);
    infile.close();
}

TR::StateBase::~StateBase()
{
    logger->flush();
    for (auto bs : branch) {
        spdlog::info("delete state: {:p} ea:{:x}-{:x}", (void*)bs, bs->get_state_ep(), bs->get_cpu_ip());
        delete bs;
    }
}

#include "spdlog/async.h"
#include "spdlog/sinks/basic_file_sink.h"

std::string get_logger_name()
{
    static int n = 0;
    char buff[50];
    std::string str;
    snprintf(buff, sizeof(buff), "sync_%d", n++);
    str.append(buff);

    return "log" + str + "_log.txt";
};


TR::StateBase::StateBase(vex_context& vctx, VexArch guest_arch)
    : m_fork_deep_num(0),
    m_state_id(0),
    m_z3_bv_const_n(0),
    m_father(nullptr),
    m_ctx(),
    m_vinfo(guest_arch),
    m_vctx(vctx),
    guest_start_ep(/*oep*/0),
    guest_start(/*oep*/0),
    m_delta(0),
    m_need_record(true),
    m_status(NewState),
    m_jump_kd(Ijk_Boring),
    solv(m_ctx),
    regs(m_ctx, REGISTER_LEN),
    mem(solv, m_ctx, true),
    branch(*this)
{
    m_vctx.set_top_state(this);
    m_vinfo.init_VexControl();
    static int n_state = 0;
    char buff[30];
    sprintf_s(buff, sizeof(buff), "top%d", n_state++);
    p_name.assign(buff);
    init_logger();
}



TR::StateBase::StateBase(StateBase& father, HWord gse)
    : m_fork_deep_num((UInt)father.m_fork_deep_num + 1),
    m_state_id((UInt)father.m_branch_state_id_max++),
    m_z3_bv_const_n((UInt)father.m_z3_bv_const_n),
    m_father(&father),
    m_ctx(),
    m_vinfo(father.m_vinfo),
    m_vctx(father.m_vctx),
    guest_start_ep(gse),
    guest_start(guest_start_ep),
    m_delta(0),
    m_need_record(father.m_need_record),
    m_status(NewState),
    m_jump_kd(Ijk_Boring),
    solv(m_ctx, father.solv, z3::solver::translate{}),
    regs(father.regs, m_ctx),
    mem(solv, m_ctx, father.mem, father.m_need_record),
    branch(*this, father.branch)
{
    p_name = father.p_name;
    init_logger();

}

void TR::StateBase::read_bin_dump(const char* binDump)
{
    const char* pname = nullptr;
    if (binDump) {
        pname = strrchr(binDump, '/');
        if(!pname) pname = strrchr(binDump, '\\');
        if (pname == NULL)
            pname = binDump;
        else
            pname++;
        p_name.assign(pname);
    }
    read_mem_dump(binDump);
    guest_start_ep = regs.get<HWord>(vinfo().gRegsIpOffset()).tor();
    guest_start = guest_start_ep;
};


UInt TR::StateBase::getStr(std::stringstream& st, HWord addr)
{
    UInt p = 0;
    while (True) {
        auto b = mem.template load<Ity_I8>(addr++);
        if (b.real()) {
            p++;
            st << (UChar)b.tor();
            if (!(UChar)b.tor()) return -1;
        }
        else {
            return p;
        }
    }
    return -1u;
}

std::string TR::StateBase::get_log_path()
{
    char buff[50];
    std::string str;
    for (StateBase* b = this->m_father; b; b = b->m_father) {
        UInt id = b->m_state_id;
        snprintf(buff, sizeof(buff), "/0x%x-0x%x", b->guest_start_ep, b->guest_start);
        str = buff + str;
    }
    snprintf(buff, sizeof(buff), "/0x%x/log.txt", guest_start_ep);
    return p_name + str + buff;
}

void TR::StateBase::init_logger()
{
    auto ln = get_logger_name();
    logger = spdlog::basic_logger_mt<spdlog::async_factory>(ln, get_log_path().c_str());
    logger->set_level(spdlog::level::info);
    logger->set_pattern("%v");
}

