
#include "state_base.h"
#include "engine/z3_target_call/z3_target_call.h"

using namespace TR;



VexGuestState* TR::StateBase::get_regs_maps()
{
    constexpr int sb = sizeof(regs_bytes);
    static_assert(REGISTER_LEN == sb, "error align");
    return reinterpret_cast<VexGuestState*>(&regs_bytes);
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
        strTemp = strContent.substr(nPos + strlen(pszOld), strContent.length());
        if (nPos == std::string::npos)
        {
            break;
        }
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
        char* data = (char*)malloc(buf.length+32);
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
            if (err = mem.map(buf.address, buf.length))
                printf("warning %s had maped before length: %llx\n", name, err);
            need_write_size += buf.length;
            write_count += mem.write_bytes(buf.address, buf.length, (unsigned char*)data);
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

TR::StateBase::~StateBase()
{
}

TR::StateBase::StateBase(vex_context& vctx, VexArch guest_arch)
    :m_ctx(),
    m_vinfo(guest_arch),
    m_vctx(vctx),
    guest_start_ep(/*oep*/0),
    guest_start(/*oep*/0),
    m_delta(0),
    m_need_record(true),
    m_z3_bv_const_n(0),
    m_status(NewState),
    m_jump_kd(Ijk_Boring),
    solv(m_ctx),
    regs(m_ctx, REGISTER_LEN),
    mem(solv, m_ctx, true),
    branch(*this)
{
    m_vctx.set_top_state(this);
    m_vinfo.ir_init();
}



TR::StateBase::StateBase(StateBase& father, HWord gse)
    : m_ctx(),
    m_vinfo(father.m_vinfo),
    m_vctx(father.m_vctx),
    guest_start_ep(gse),
    guest_start(guest_start_ep),
    m_delta(0),
    m_need_record(father.m_need_record),
    m_z3_bv_const_n((UInt)father.m_z3_bv_const_n),
    m_status(NewState),
    m_jump_kd(Ijk_Boring),
    solv(m_ctx, father.solv, z3::solver::translate{}),
    regs(father.regs, m_ctx),
    mem(solv, m_ctx, father.mem, father.m_need_record),
    branch(*this, father.branch)
{

}

void TR::StateBase::read_bin_dump(const char* binDump)
{
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

bool TR::operator==(InvocationStack<HWord> const& a, InvocationStack<HWord> const& b)
{
    return (a.get_guest_call_stack() == b.get_guest_call_stack()) && (a.get_guest_stack() == b.get_guest_stack());
}

std::ostream& TR::operator<<(std::ostream& out, const TR::StateBase& n)
{
    return out << (std::string)n;
}

std::ostream& TR::operator<<(std::ostream& out, const TR::InvocationStack<HWord>& e)
{
    return out << (std::string)e;
}
