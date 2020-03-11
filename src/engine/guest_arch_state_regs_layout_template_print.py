PPC64 = """

typedef
   struct {
     /* Event check fail addr, counter, and padding to make GPR0 16
        aligned. */
      /*   0 */ ULong  host_EvC_FAILADDR;
      /*   8 */ UInt   host_EvC_COUNTER;
      /*  12 */ UInt   pad0;
      /* Add 16 to all of the offsets below .. */
      /* General Purpose Registers */
      /*   0 */ ULong guest_GPR0;
      /*   8 */ ULong guest_GPR1;
      /*  16 */ ULong guest_GPR2;
      /*  24 */ ULong guest_GPR3;
      /*  32 */ ULong guest_GPR4;
      /*  40 */ ULong guest_GPR5;
      /*  48 */ ULong guest_GPR6;
      /*  56 */ ULong guest_GPR7;
      /*  64 */ ULong guest_GPR8;
      /*  72 */ ULong guest_GPR9;
      /*  80 */ ULong guest_GPR10;
      /*  88 */ ULong guest_GPR11;
      /*  96 */ ULong guest_GPR12;
      /* 104 */ ULong guest_GPR13;
      /* 112 */ ULong guest_GPR14;
      /* 120 */ ULong guest_GPR15;
      /* 128 */ ULong guest_GPR16;
      /* 136 */ ULong guest_GPR17;
      /* 144 */ ULong guest_GPR18;
      /* 152 */ ULong guest_GPR19;
      /* 160 */ ULong guest_GPR20;
      /* 168 */ ULong guest_GPR21;
      /* 176 */ ULong guest_GPR22;
      /* 184 */ ULong guest_GPR23;
      /* 192 */ ULong guest_GPR24;
      /* 200 */ ULong guest_GPR25;
      /* 208 */ ULong guest_GPR26;
      /* 216 */ ULong guest_GPR27;
      /* 224 */ ULong guest_GPR28;
      /* 232 */ ULong guest_GPR29;
      /* 240 */ ULong guest_GPR30;
      /* 248 */ ULong guest_GPR31;

      // Vector Registers, Floating Point Registers, and VSX Registers
      // With ISA 2.06, the "Vector-Scalar Floating-point" category
      // provides facilities to support vector and scalar binary floating-
      // point operations.  A unified register file is an integral part
      // of this new facility, combining floating point and vector registers
      // using a 64x128-bit vector.  These are referred to as VSR[0..63].
      // The floating point registers are now mapped into double word element 0
      // of VSR[0..31]. The 32x128-bit vector registers defined by the "Vector
      // Facility [Category: Vector]" are now mapped to VSR[32..63].

      // IMPORTANT: the user of libvex must place the guest state so as
      // to ensure that guest_VSR{0..63}, and any shadows thereof, are
      // 16-aligned.

      /*  256 */ U128 guest_VSR0;
      /*  272 */ U128 guest_VSR1;
      /*  288 */ U128 guest_VSR2;
      /*  304 */ U128 guest_VSR3;
      /*  320 */ U128 guest_VSR4;
      /*  336 */ U128 guest_VSR5;
      /*  352 */ U128 guest_VSR6;
      /*  368 */ U128 guest_VSR7;
      /*  384 */ U128 guest_VSR8;
      /*  400 */ U128 guest_VSR9;
      /*  416 */ U128 guest_VSR10;
      /*  432 */ U128 guest_VSR11;
      /*  448 */ U128 guest_VSR12;
      /*  464 */ U128 guest_VSR13;
      /*  480 */ U128 guest_VSR14;
      /*  496 */ U128 guest_VSR15;
      /*  512 */ U128 guest_VSR16;
      /*  528 */ U128 guest_VSR17;
      /*  544 */ U128 guest_VSR18;
      /*  560 */ U128 guest_VSR19;
      /*  576 */ U128 guest_VSR20;
      /*  592 */ U128 guest_VSR21;
      /*  608 */ U128 guest_VSR22;
      /*  624 */ U128 guest_VSR23;
      /*  640 */ U128 guest_VSR24;
      /*  656 */ U128 guest_VSR25;
      /*  672 */ U128 guest_VSR26;
      /*  688 */ U128 guest_VSR27;
      /*  704 */ U128 guest_VSR28;
      /*  720 */ U128 guest_VSR29;
      /*  736 */ U128 guest_VSR30;
      /*  752 */ U128 guest_VSR31;
      /*  768 */ U128 guest_VSR32;
      /*  784 */ U128 guest_VSR33;
      /*  800 */ U128 guest_VSR34;
      /*  816 */ U128 guest_VSR35;
      /*  832 */ U128 guest_VSR36;
      /*  848 */ U128 guest_VSR37;
      /*  864 */ U128 guest_VSR38;
      /*  880 */ U128 guest_VSR39;
      /*  896 */ U128 guest_VSR40;
      /*  912 */ U128 guest_VSR41;
      /*  928 */ U128 guest_VSR42;
      /*  944 */ U128 guest_VSR43;
      /*  960 */ U128 guest_VSR44;
      /*  976 */ U128 guest_VSR45;
      /*  992 */ U128 guest_VSR46;
      /* 1008 */ U128 guest_VSR47;
      /* 1024 */ U128 guest_VSR48;
      /* 1040 */ U128 guest_VSR49;
      /* 1056 */ U128 guest_VSR50;
      /* 1072 */ U128 guest_VSR51;
      /* 1088 */ U128 guest_VSR52;
      /* 1104 */ U128 guest_VSR53;
      /* 1120 */ U128 guest_VSR54;
      /* 1136 */ U128 guest_VSR55;
      /* 1152 */ U128 guest_VSR56;
      /* 1168 */ U128 guest_VSR57;
      /* 1184 */ U128 guest_VSR58;
      /* 1200 */ U128 guest_VSR59;
      /* 1216 */ U128 guest_VSR60;
      /* 1232 */ U128 guest_VSR61;
      /* 1248 */ U128 guest_VSR62;
      /* 1264 */ U128 guest_VSR63;

      /* 1280 */ ULong guest_CIA;    // IP (no arch visible register)
      /* 1288 */ ULong guest_LR;     // Link Register
      /* 1296 */ ULong guest_CTR;    // Count Register

      /* XER pieces */
      /* 1304 */ UChar guest_XER_SO; /* in lsb */
      /* 1305 */ UChar guest_XER_OV; /* in lsb */
      /* 1306 */ UChar guest_XER_OV32; /* in lsb */
      /* 1307 */ UChar guest_XER_CA; /* in lsb */
      /* 1308 */ UChar guest_XER_CA32; /* in lsb */
      /* 1309 */ UChar guest_XER_BC; /* all bits */

      /* CR pieces */
      /* 1310 */ UChar guest_CR0_321; /* in [3:1] */
      /* 1311 */ UChar guest_CR0_0;   /* in lsb */
      /* 1312 */ UChar guest_CR1_321; /* in [3:1] */
      /* 1313 */ UChar guest_CR1_0;   /* in lsb */
      /* 1314 */ UChar guest_CR2_321; /* in [3:1] */
      /* 1315 */ UChar guest_CR2_0;   /* in lsb */
      /* 1316 */ UChar guest_CR3_321; /* in [3:1] */
      /* 1317 */ UChar guest_CR3_0;   /* in lsb */
      /* 1318 */ UChar guest_CR4_321; /* in [3:1] */
      /* 1319 */ UChar guest_CR4_0;   /* in lsb */
      /* 1320 */ UChar guest_CR5_321; /* in [3:1] */
      /* 1321 */ UChar guest_CR5_0;   /* in lsb */
      /* 1322 */ UChar guest_CR6_321; /* in [3:1] */
      /* 1323 */ UChar guest_CR6_0;   /* in lsb */
      /* 1324 */ UChar guest_CR7_321; /* in [3:1] */
      /* 1325 */ UChar guest_CR7_0;   /* in lsb */

      /* FP Status and  Control Register fields. Only rounding mode fields
       * and Floating-point Condition Code (FPCC) fields are supported.
       */
      /* 1326 */ UChar guest_FPROUND; // Binary Floating Point Rounding Mode
      /* 1327 */ UChar guest_DFPROUND; // Decimal Floating Point Rounding Mode
      /* 1328 */ UChar guest_C_FPCC;   // Floating-point Condition Code
                                       // and Floating-point Condition Code

      /* 1329 */ UChar pad2;
      /* 1330 */ UChar pad3;
      /* 1331 */ UChar pad4;

      /* Vector Save/Restore Register */
      /* 1332 */ UInt guest_VRSAVE;

      /* Vector Status and Control Register */
      /* 1336 */ UInt guest_VSCR;

      /* Emulation notes */
      /* 1340 */ UInt guest_EMNOTE;

      /* gcc adds 4 bytes padding here: pre-empt it. */
      /* 1344 */ UInt  padding;

      /* For icbi: record start and length of area to invalidate */
      /* 1348 */ ULong guest_CMSTART;
      /* 1356 */ ULong guest_CMLEN;

      /* Used to record the unredirected guest address at the start of
         a translation whose start has been redirected.  By reading
         this pseudo-register shortly afterwards, the translation can
         find out what the corresponding no-redirection address was.
         Note, this is only set for wrap-style redirects, not for
         replace-style ones. */
      /* 1364 */ ULong guest_NRADDR;
      /* 1372 */ ULong guest_NRADDR_GPR2;

     /* A grows-upwards stack for hidden saves/restores of LR and R2
        needed for function interception and wrapping on ppc64-linux.
        A horrible hack.  REDIR_SP points to the highest live entry,
        and so starts at -1. */
      /* 1380 */ ULong guest_REDIR_SP;
      /* 1388 */ ULong guest_REDIR_STACK[VEX_GUEST_PPC64_REDIR_STACK_SIZE];

      /* Needed for Darwin: CIA at the last SC insn.  Used when backing up
         to restart a syscall that has been interrupted by a signal. */
      /* 1646 */ ULong guest_IP_AT_SYSCALL;

      /* SPRG3, which AIUI is readonly in user space.  Needed for
         threading on AIX. */
      /* 1654 */ ULong guest_SPRG3_RO;

      /* 1662 */ ULong guest_TFHAR;     // Transaction Failure Handler Address Register
      /* 1670 */ ULong guest_TEXASR;    // Transaction EXception And Summary Register
      /* 1678 */ ULong guest_TFIAR;     // Transaction Failure Instruction Address Register
      /* 1686 */ ULong guest_PPR;       // Program Priority register
      /* 1694 */ UInt  guest_TEXASRU;   // Transaction EXception And Summary Register Upper
      /* 1698 */ UInt  guest_PSPB;      // Problem State Priority Boost register
      /* 1702 */ ULong guest_DSCR;      // Data Stream Control register

      /* Padding to make it have an 16-aligned size */
      /* 1710 */   UInt  padding1;
      /* 1714 */   UInt  padding2;
      /* 1718 */   UInt  padding3;

   }
   VexGuestPPC64State;
"""


PPC32 = """

typedef
   struct {
      /* Event check fail addr and counter. */
      /*   0 */ UInt host_EvC_FAILADDR;
      /*   4 */ UInt host_EvC_COUNTER;
      /*   8 */ UInt pad3;
      /*  12 */ UInt pad4; 
      /* Add 16 to all the numbers below.  Sigh. */
      /* General Purpose Registers */
      /*   0 */ UInt guest_GPR0;
      /*   4 */ UInt guest_GPR1;
      /*   8 */ UInt guest_GPR2;
      /*  12 */ UInt guest_GPR3;
      /*  16 */ UInt guest_GPR4;
      /*  20 */ UInt guest_GPR5;
      /*  24 */ UInt guest_GPR6;
      /*  28 */ UInt guest_GPR7;
      /*  32 */ UInt guest_GPR8;
      /*  36 */ UInt guest_GPR9;
      /*  40 */ UInt guest_GPR10;
      /*  44 */ UInt guest_GPR11;
      /*  48 */ UInt guest_GPR12;
      /*  52 */ UInt guest_GPR13;
      /*  56 */ UInt guest_GPR14;
      /*  60 */ UInt guest_GPR15;
      /*  64 */ UInt guest_GPR16;
      /*  68 */ UInt guest_GPR17;
      /*  72 */ UInt guest_GPR18;
      /*  76 */ UInt guest_GPR19;
      /*  80 */ UInt guest_GPR20;
      /*  84 */ UInt guest_GPR21;
      /*  88 */ UInt guest_GPR22;
      /*  92 */ UInt guest_GPR23;
      /*  96 */ UInt guest_GPR24;
      /* 100 */ UInt guest_GPR25;
      /* 104 */ UInt guest_GPR26;
      /* 108 */ UInt guest_GPR27;
      /* 112 */ UInt guest_GPR28;
      /* 116 */ UInt guest_GPR29;
      /* 120 */ UInt guest_GPR30;
      /* 124 */ UInt guest_GPR31;

      // Vector Registers, Floating Point Registers, and VSX Registers
      // With ISA 2.06, the "Vector-Scalar Floating-point" category
      // provides facilities to support vector and scalar binary floating-
      // point operations.  A unified register file is an integral part
      // of this new facility, combining floating point and vector registers
      // using a 64x128-bit vector.  These are referred to as VSR[0..63].
      // The floating point registers are now mapped into double word element 0
      // of VSR[0..31]. The 32x128-bit vector registers defined by the "Vector
      // Facility [Category: Vector]" are now mapped to VSR[32..63].

      // IMPORTANT: the user of libvex must place the guest state so as
      // to ensure that guest_VSR{0..63}, and any shadows thereof, are
      // 16-aligned.

      /*  128 */ U128 guest_VSR0;
      /*  144 */ U128 guest_VSR1;
      /*  160 */ U128 guest_VSR2;
      /*  176 */ U128 guest_VSR3;
      /*  192 */ U128 guest_VSR4;
      /*  208 */ U128 guest_VSR5;
      /*  224 */ U128 guest_VSR6;
      /*  240 */ U128 guest_VSR7;
      /*  256 */ U128 guest_VSR8;
      /*  272 */ U128 guest_VSR9;
      /*  288 */ U128 guest_VSR10;
      /*  304 */ U128 guest_VSR11;
      /*  320 */ U128 guest_VSR12;
      /*  336 */ U128 guest_VSR13;
      /*  352 */ U128 guest_VSR14;
      /*  368 */ U128 guest_VSR15;
      /*  384 */ U128 guest_VSR16;
      /*  400 */ U128 guest_VSR17;
      /*  416 */ U128 guest_VSR18;
      /*  432 */ U128 guest_VSR19;
      /*  448 */ U128 guest_VSR20;
      /*  464 */ U128 guest_VSR21;
      /*  480 */ U128 guest_VSR22;
      /*  496 */ U128 guest_VSR23;
      /*  512 */ U128 guest_VSR24;
      /*  528 */ U128 guest_VSR25;
      /*  544 */ U128 guest_VSR26;
      /*  560 */ U128 guest_VSR27;
      /*  576 */ U128 guest_VSR28;
      /*  592 */ U128 guest_VSR29;
      /*  608 */ U128 guest_VSR30;
      /*  624 */ U128 guest_VSR31;
      /*  640 */ U128 guest_VSR32;
      /*  656 */ U128 guest_VSR33;
      /*  672 */ U128 guest_VSR34;
      /*  688 */ U128 guest_VSR35;
      /*  704 */ U128 guest_VSR36;
      /*  720 */ U128 guest_VSR37;
      /*  736 */ U128 guest_VSR38;
      /*  752 */ U128 guest_VSR39;
      /*  768 */ U128 guest_VSR40;
      /*  784 */ U128 guest_VSR41;
      /*  800 */ U128 guest_VSR42;
      /*  816 */ U128 guest_VSR43;
      /*  832 */ U128 guest_VSR44;
      /*  848 */ U128 guest_VSR45;
      /*  864 */ U128 guest_VSR46;
      /*  880 */ U128 guest_VSR47;
      /*  896 */ U128 guest_VSR48;
      /*  912 */ U128 guest_VSR49;
      /*  928 */ U128 guest_VSR50;
      /*  944 */ U128 guest_VSR51;
      /*  960 */ U128 guest_VSR52;
      /*  976 */ U128 guest_VSR53;
      /*  992 */ U128 guest_VSR54;
      /* 1008 */ U128 guest_VSR55;
      /* 1024 */ U128 guest_VSR56;
      /* 1040 */ U128 guest_VSR57;
      /* 1056 */ U128 guest_VSR58;
      /* 1072 */ U128 guest_VSR59;
      /* 1088 */ U128 guest_VSR60;
      /* 1104 */ U128 guest_VSR61;
      /* 1120 */ U128 guest_VSR62;
      /* 1136 */ U128 guest_VSR63;

      /* 1152 */ UInt guest_CIA;    // IP (no arch visible register)
      /* 1156 */ UInt guest_LR;     // Link Register
      /* 1160 */ UInt guest_CTR;    // Count Register

      /* XER pieces */
      /* 1164 */ UChar guest_XER_SO; /* in lsb */
      /* 1165 */ UChar guest_XER_OV; /* in lsb */
      /* 1166 */ UChar guest_XER_OV32; /* in lsb */
      /* 1167 */ UChar guest_XER_CA; /* in lsb */
      /* 1168 */ UChar guest_XER_CA32; /* in lsb */
      /* 1169 */ UChar guest_XER_BC; /* all bits */

      /* CR pieces */
      /* 1170 */ UChar guest_CR0_321; /* in [3:1] */
      /* 1171 */ UChar guest_CR0_0;   /* in lsb */
      /* 1172 */ UChar guest_CR1_321; /* in [3:1] */
      /* 1173 */ UChar guest_CR1_0;   /* in lsb */
      /* 1174 */ UChar guest_CR2_321; /* in [3:1] */
      /* 1175 */ UChar guest_CR2_0;   /* in lsb */
      /* 1176 */ UChar guest_CR3_321; /* in [3:1] */
      /* 1177 */ UChar guest_CR3_0;   /* in lsb */
      /* 1178 */ UChar guest_CR4_321; /* in [3:1] */
      /* 1179 */ UChar guest_CR4_0;   /* in lsb */
      /* 1180 */ UChar guest_CR5_321; /* in [3:1] */
      /* 1181 */ UChar guest_CR5_0;   /* in lsb */
      /* 1182 */ UChar guest_CR6_321; /* in [3:1] */
      /* 1183 */ UChar guest_CR6_0;   /* in lsb */
      /* 1184 */ UChar guest_CR7_321; /* in [3:1] */
      /* 1185 */ UChar guest_CR7_0;   /* in lsb */

      /* FP Status and  Control Register fields. Only rounding mode fields
       * and Floating-point Condition Code (FPCC) fields in the FPSCR are
       * supported.
       */
      /* 1186 */ UChar guest_FPROUND; // Binary Floating Point Rounding Mode
      /* 1187 */ UChar guest_DFPROUND; // Decimal Floating Point Rounding Mode
      /* 1188 */ UChar guest_C_FPCC;   // Floating-Point Result Class Descriptor
                                       // and Floating-point Condition Code
      /* 1189 */ UChar pad0;
      /* 1190 */ UChar pad1;
      /* 1191 */ UChar pad2;

      /* Vector Save/Restore Register */
      /* 1192 */ UInt guest_VRSAVE;

      /* Vector Status and Control Register */
      /* 1196 */ UInt guest_VSCR;

      /* Emulation notes */
      /* 1200 */ UInt guest_EMNOTE;

      /* For icbi: record start and length of area to invalidate */
      /* 1204 */ UInt guest_CMSTART;
      /* 1208 */ UInt guest_CMLEN;

      /* Used to record the unredirected guest address at the start of
         a translation whose start has been redirected.  By reading
         this pseudo-register shortly afterwards, the translation can
         find out what the corresponding no-redirection address was.
         Note, this is only set for wrap-style redirects, not for
         replace-style ones. */
      /* 1212 */ UInt guest_NRADDR;
      /* 1216 */ UInt guest_NRADDR_GPR2; /* needed by aix */

     /* A grows-upwards stack for hidden saves/restores of LR and R2
        needed for function interception and wrapping on ppc32-aix5.
        A horrible hack.  REDIR_SP points to the highest live entry,
        and so starts at -1. */
      /* 1220 */ UInt guest_REDIR_SP;
      /* 1224 */ UInt guest_REDIR_STACK[VEX_GUEST_PPC32_REDIR_STACK_SIZE];

      /* Needed for Darwin (but mandated for all guest architectures):
         CIA at the last SC insn.  Used when backing up to restart a
         syscall that has been interrupted by a signal. */
      /* 134C */ UInt guest_IP_AT_SYSCALL;

      /* SPRG3, which AIUI is readonly in user space.  Needed for
         threading on AIX. */
      /* 1356 */ UInt guest_SPRG3_RO;
      /* 1360 */ UInt  padding1;
      /* 1364 */ ULong guest_TFHAR;     // Transaction Failure Handler Address Register
      /* 1372 */ ULong guest_TEXASR;    // Transaction EXception And Summary Register
      /* 1380 */ ULong guest_TFIAR;     // Transaction Failure Instruction Address Register
      /* 1388 */ ULong guest_PPR;       // Program Priority register
      /* 1396 */ UInt  guest_TEXASRU;   // Transaction EXception And Summary Register Upper
      /* 1400 */ UInt  guest_PSPB;      // Problem State Priority Boost register
      /* 1404 */ ULong guest_DSCR;      // Data Stream Control register
      /* Padding to make it have an 16-aligned size */
      /* 1408 */ UInt  padding3;
      /* 1412 */ UInt  padding4;
   }
   VexGuestPPC32State;


"""



ARM="""
typedef
   struct {
      /* 0 */
      /* Event check fail addr and counter. */
      UInt host_EvC_FAILADDR; /* 0 */
      UInt host_EvC_COUNTER;  /* 4 */
      UInt guest_R0;
      UInt guest_R1;
      UInt guest_R2;
      UInt guest_R3;
      UInt guest_R4;
      UInt guest_R5;
      UInt guest_R6;
      UInt guest_R7;
      UInt guest_R8;
      UInt guest_R9;
      UInt guest_R10;
      UInt guest_R11;
      UInt guest_R12;
      UInt guest_R13;     /* stack pointer */
      UInt guest_R14;     /* link register */
      UInt guest_R15T;
      /* program counter[31:1] ++ [T], encoding both the current
         instruction address and the ARM vs Thumb state of the
         machine.  T==1 is Thumb, T==0 is ARM.  Hence values of the
         form X--(31)--X1 denote a Thumb instruction at location
         X--(31)--X0, values of the form X--(30)--X00 denote an ARM
         instruction at precisely that address, and values of the form
         X--(30)--10 are invalid since they would imply an ARM
         instruction at a non-4-aligned address. */

      /* 4-word thunk used to calculate N(sign) Z(zero) C(carry,
         unsigned overflow) and V(signed overflow) flags. */
      /* 72 */
      UInt guest_CC_OP;
      UInt guest_CC_DEP1;
      UInt guest_CC_DEP2;
      UInt guest_CC_NDEP;

      /* A 32-bit value which is used to compute the APSR.Q (sticky
         saturation) flag, when necessary.  If the value stored here
         is zero, APSR.Q is currently zero.  If it is any other value,
         APSR.Q is currently one. */
      UInt guest_QFLAG32;

      /* 32-bit values to represent APSR.GE0 .. GE3.  Same
         zero-vs-nonzero scheme as for QFLAG32. */
      UInt guest_GEFLAG0;
      UInt guest_GEFLAG1;
      UInt guest_GEFLAG2;
      UInt guest_GEFLAG3;

      /* Various pseudo-regs mandated by Vex or Valgrind. */
      /* Emulation notes */
      UInt guest_EMNOTE;

      /* For clinval/clflush: record start and length of area */
      UInt guest_CMSTART;
      UInt guest_CMLEN;

      /* Used to record the unredirected guest address at the start of
         a translation whose start has been redirected.  By reading
         this pseudo-register shortly afterwards, the translation can
         find out what the corresponding no-redirection address was.
         Note, this is only set for wrap-style redirects, not for
         replace-style ones. */
      UInt guest_NRADDR;

      /* Needed for Darwin (but mandated for all guest architectures):
         program counter at the last syscall insn (int 0x80/81/82,
         sysenter, syscall, svc).  Used when backing up to restart a
         syscall that has been interrupted by a signal. */
      /* 124 */
      UInt guest_IP_AT_SYSCALL;

      /* VFP state.  D0 .. D15 must be 8-aligned. */
      /* 128 */
      ULong guest_D0;
      ULong guest_D1;
      ULong guest_D2;
      ULong guest_D3;
      ULong guest_D4;
      ULong guest_D5;
      ULong guest_D6;
      ULong guest_D7;
      ULong guest_D8;
      ULong guest_D9;
      ULong guest_D10;
      ULong guest_D11;
      ULong guest_D12;
      ULong guest_D13;
      ULong guest_D14;
      ULong guest_D15;
      ULong guest_D16;
      ULong guest_D17;
      ULong guest_D18;
      ULong guest_D19;
      ULong guest_D20;
      ULong guest_D21;
      ULong guest_D22;
      ULong guest_D23;
      ULong guest_D24;
      ULong guest_D25;
      ULong guest_D26;
      ULong guest_D27;
      ULong guest_D28;
      ULong guest_D29;
      ULong guest_D30;
      ULong guest_D31;
      UInt  guest_FPSCR;

      /* Not a town in Cornwall, but instead the TPIDRURO, on of the
         Thread ID registers present in CP15 (the system control
         coprocessor), register set "c13", register 3 (the User
         Read-only Thread ID Register).  arm-linux apparently uses it
         to hold the TLS pointer for the thread.  It's read-only in
         user space.  On Linux it is set in user space by various
         thread-related syscalls. */
      UInt guest_TPIDRURO;

      /* TPIDRURW is also apparently used as a thread register, but one
         controlled entirely by, and writable from, user space.  We model
         it as a completely vanilla piece of integer state. */
      UInt guest_TPIDRURW;

      /* Representation of the Thumb IT state.  ITSTATE is a 32-bit
         value with 4 8-bit lanes.  [7:0] pertain to the next insn to
         execute, [15:8] for the one after that, etc.  The per-insn
         update to ITSTATE is to unsignedly shift it right 8 bits,
         hence introducing a zero byte for the furthest ahead
         instruction.  As per the next para, a zero byte denotes the
         condition ALWAYS.

         Each byte lane has one of the two following formats:

         cccc 0001  for an insn which is part of an IT block.  cccc is
                    the guarding condition (standard ARM condition
                    code) XORd with 0xE, so as to cause 'cccc == 0'
                    to encode the condition ALWAYS.

         0000 0000  for an insn which is not part of an IT block.

         If the bottom 4 bits are zero then the top 4 must be too.

         Given the byte lane for an instruction, the guarding
         condition for the instruction is (((lane >> 4) & 0xF) ^ 0xE).
         This is not as stupid as it sounds, because the front end
         elides the shift.  And the am-I-in-an-IT-block check is
         (lane != 0).

         In the case where (by whatever means) we know at JIT time
         that an instruction is not in an IT block, we can prefix its
         IR with assignments ITSTATE = 0 and hence have iropt fold out
         the testing code.

         The condition "is outside or last in IT block" corresponds
         to the top 24 bits of ITSTATE being zero.
      */
      UInt guest_ITSTATE;
   }
   VexGuestARMState;
"""

ARM64="""
typedef
   struct {
      /* Event check fail addr and counter. */
      /* 0 */  ULong host_EvC_FAILADDR;
      /* 8 */  UInt  host_EvC_COUNTER;
      /* 12 */ UInt  pad0;
      /* 16 */
      ULong guest_X0;
      ULong guest_X1;
      ULong guest_X2;
      ULong guest_X3;
      ULong guest_X4;
      ULong guest_X5;
      ULong guest_X6;
      ULong guest_X7;
      ULong guest_X8;
      ULong guest_X9;
      ULong guest_X10;
      ULong guest_X11;
      ULong guest_X12;
      ULong guest_X13;
      ULong guest_X14;
      ULong guest_X15;
      ULong guest_X16;
      ULong guest_X17;
      ULong guest_X18;
      ULong guest_X19;
      ULong guest_X20;
      ULong guest_X21;
      ULong guest_X22;
      ULong guest_X23;
      ULong guest_X24;
      ULong guest_X25;
      ULong guest_X26;
      ULong guest_X27;
      ULong guest_X28;
      ULong guest_X29;
      ULong guest_X30;     /* link register */
      ULong guest_XSP;
      ULong guest_PC;

      /* 4-word thunk used to calculate N(sign) Z(zero) C(carry,
         unsigned overflow) and V(signed overflow) flags. */
      ULong guest_CC_OP;
      ULong guest_CC_DEP1;
      ULong guest_CC_DEP2;
      ULong guest_CC_NDEP;

      /* User-space thread register? */
      ULong guest_TPIDR_EL0;

      /* FP/SIMD state */
      U128 guest_Q0;
      U128 guest_Q1;
      U128 guest_Q2;
      U128 guest_Q3;
      U128 guest_Q4;
      U128 guest_Q5;
      U128 guest_Q6;
      U128 guest_Q7;
      U128 guest_Q8;
      U128 guest_Q9;
      U128 guest_Q10;
      U128 guest_Q11;
      U128 guest_Q12;
      U128 guest_Q13;
      U128 guest_Q14;
      U128 guest_Q15;
      U128 guest_Q16;
      U128 guest_Q17;
      U128 guest_Q18;
      U128 guest_Q19;
      U128 guest_Q20;
      U128 guest_Q21;
      U128 guest_Q22;
      U128 guest_Q23;
      U128 guest_Q24;
      U128 guest_Q25;
      U128 guest_Q26;
      U128 guest_Q27;
      U128 guest_Q28;
      U128 guest_Q29;
      U128 guest_Q30;
      U128 guest_Q31;

      /* A 128-bit value which is used to represent the FPSR.QC (sticky
         saturation) flag, when necessary.  If the value stored here
         is zero, FPSR.QC is currently zero.  If it is any other value,
         FPSR.QC is currently one.  We don't currently represent any 
         other bits of FPSR, so this is all that that is for FPSR. */
      U128 guest_QCFLAG;

      /* Various pseudo-regs mandated by Vex or Valgrind. */
      /* Emulation notes */
      UInt guest_EMNOTE;

      /* For clflush/clinval: record start and length of area */
      ULong guest_CMSTART;
      ULong guest_CMLEN;

      /* Used to record the unredirected guest address at the start of
         a translation whose start has been redirected.  By reading
         this pseudo-register shortly afterwards, the translation can
         find out what the corresponding no-redirection address was.
         Note, this is only set for wrap-style redirects, not for
         replace-style ones. */
      ULong guest_NRADDR;

      /* Needed for Darwin (but mandated for all guest architectures):
         program counter at the last syscall insn (int 0x80/81/82,
         sysenter, syscall, svc).  Used when backing up to restart a
         syscall that has been interrupted by a signal. */
      ULong guest_IP_AT_SYSCALL;

      /* The complete FPCR.  Default value seems to be zero.  We
         ignore all bits except 23 and 22, which are the rounding
         mode.  The guest is unconstrained in what values it can write
         to and read from this register, but the emulation only takes
         note of bits 23 and 22. */
      UInt  guest_FPCR;

      /* Fallback LL/SC support.  See bugs 344524 and 369459. */
      ULong guest_LLSC_SIZE; // 0==no current transaction, else 1,2,4 or 8.
      ULong guest_LLSC_ADDR; // Address of transaction.
      ULong guest_LLSC_DATA; // Original value at _ADDR, zero-extended.

      /* Padding to make it have an 16-aligned size */
      /* UInt  pad_end_0; */
      ULong pad_end_1;
   }
   VexGuestARM64State;
   """



X86="""
typedef
   struct {
      /* Event check fail addr and counter. */
      UInt  host_EvC_FAILADDR; /* 0 */
      UInt  host_EvC_COUNTER;  /* 4 */
      UInt  guest_EAX;         /* 8 */
      UInt  guest_ECX;
      UInt  guest_EDX;
      UInt  guest_EBX;
      UInt  guest_ESP;
      UInt  guest_EBP;
      UInt  guest_ESI;
      UInt  guest_EDI;         /* 36 */

      /* 4-word thunk used to calculate O S Z A C P flags. */
      UInt  guest_CC_OP;       /* 40 */
      UInt  guest_CC_DEP1;
      UInt  guest_CC_DEP2;
      UInt  guest_CC_NDEP;     /* 52 */
      /* The D flag is stored here, encoded as either -1 or +1 */
      UInt  guest_DFLAG;       /* 56 */
      /* Bit 21 (ID) of eflags stored here, as either 0 or 1. */
      UInt  guest_IDFLAG;      /* 60 */
      /* Bit 18 (AC) of eflags stored here, as either 0 or 1. */
      UInt  guest_ACFLAG;      /* 64 */

      /* EIP */
      UInt  guest_EIP;         /* 68 */

      /* FPU */
      ULong guest_FPREG[8];    /* 72 */
      UChar guest_FPTAG[8];   /* 136 */
      UInt  guest_FPROUND;    /* 144 */
      UInt  guest_FC3210;     /* 148 */
      UInt  guest_FTOP;       /* 152 */

      /* SSE */
      UInt  guest_SSEROUND;   /* 156 */
      U128  guest_XMM0;       /* 160 */
      U128  guest_XMM1;
      U128  guest_XMM2;
      U128  guest_XMM3;
      U128  guest_XMM4;
      U128  guest_XMM5;
      U128  guest_XMM6;
      U128  guest_XMM7;

      /* Segment registers. */
      UShort guest_CS;
      UShort guest_DS;
      UShort guest_ES;
      UShort guest_FS;
      UShort guest_GS;
      UShort guest_SS;
      /* LDT/GDT stuff. */
      ULong  guest_LDT; /* host addr, a VexGuestX86SegDescr* */
      ULong  guest_GDT; /* host addr, a VexGuestX86SegDescr* */

      /* Emulation notes */
      UInt   guest_EMNOTE;

      /* For clflush/clinval: record start and length of area */
      UInt guest_CMSTART;
      UInt guest_CMLEN;

      /* Used to record the unredirected guest address at the start of
         a translation whose start has been redirected.  By reading
         this pseudo-register shortly afterwards, the translation can
         find out what the corresponding no-redirection address was.
         Note, this is only set for wrap-style redirects, not for
         replace-style ones. */
      UInt guest_NRADDR;

      /* Used for Darwin syscall dispatching. */
      UInt guest_SC_CLASS;

      /* Needed for Darwin (but mandated for all guest architectures):
         EIP at the last syscall insn (int 0x80/81/82, sysenter,
         syscall).  Used when backing up to restart a syscall that has
         been interrupted by a signal. */
      UInt guest_IP_AT_SYSCALL;

      /* Padding to make it have an 16-aligned size */
      UInt padding1;
      UInt padding2;
      UInt padding3;
   }
   VexGuestX86State;
   """



MIPS32 = """

typedef
   struct {
      /*    0 */ UInt host_EvC_FAILADDR;
      /*    4 */ UInt host_EvC_COUNTER;

      /* CPU Registers */
      /*    8 */ UInt guest_r0;   /* Hardwired to 0. */
      /*   12 */ UInt guest_r1;   /* Assembler temporary */
      /*   16 */ UInt guest_r2;   /* Values for function returns ...*/
      /*   20 */ UInt guest_r3;   /* ... and expression evaluation */
      /*   24 */ UInt guest_r4;   /* Function arguments */
      /*   28 */ UInt guest_r5;
      /*   32 */ UInt guest_r6;
      /*   36 */ UInt guest_r7;
      /*   40 */ UInt guest_r8;   /* Temporaries */
      /*   44 */ UInt guest_r9;
      /*   48 */ UInt guest_r10;
      /*   52 */ UInt guest_r11;
      /*   56 */ UInt guest_r12;
      /*   60 */ UInt guest_r13;
      /*   64 */ UInt guest_r14;
      /*   68 */ UInt guest_r15;
      /*   72 */ UInt guest_r16;  /* Saved temporaries */
      /*   76 */ UInt guest_r17;
      /*   80 */ UInt guest_r18;
      /*   84 */ UInt guest_r19;
      /*   88 */ UInt guest_r20;
      /*   92 */ UInt guest_r21;
      /*   96 */ UInt guest_r22;
      /*  100 */ UInt guest_r23;
      /*  104 */ UInt guest_r24;  /* Temporaries */
      /*  108 */ UInt guest_r25;
      /*  112 */ UInt guest_r26;  /* Reserved for OS kernel */
      /*  116 */ UInt guest_r27;
      /*  120 */ UInt guest_r28;  /* Global pointer */
      /*  124 */ UInt guest_r29;  /* Stack pointer */
      /*  128 */ UInt guest_r30;  /* Frame pointer */
      /*  132 */ UInt guest_r31;  /* Return address */
      /*  136 */ UInt guest_PC;   /* Program counter */
      /*  140 */ UInt guest_HI;   /* Multiply and divide reg higher result */
      /*  144 */ UInt guest_LO;   /* Multiply and divide reg lower result */
      /*  148 */ UInt _padding1;

      /* FPU Registers */
      /*  152 */ ULong guest_f0;  /* Floating point general purpose registers */
      /*  160 */ ULong guest_f1;
      /*  168 */ ULong guest_f2;
      /*  176 */ ULong guest_f3;
      /*  184 */ ULong guest_f4;
      /*  192 */ ULong guest_f5;
      /*  200 */ ULong guest_f6;
      /*  208 */ ULong guest_f7;
      /*  216 */ ULong guest_f8;
      /*  224 */ ULong guest_f9;
      /*  232 */ ULong guest_f10;
      /*  240 */ ULong guest_f11;
      /*  248 */ ULong guest_f12;
      /*  256 */ ULong guest_f13;
      /*  264 */ ULong guest_f14;
      /*  272 */ ULong guest_f15;
      /*  280 */ ULong guest_f16;
      /*  288 */ ULong guest_f17;
      /*  296 */ ULong guest_f18;
      /*  304 */ ULong guest_f19;
      /*  312 */ ULong guest_f20;
      /*  320 */ ULong guest_f21;
      /*  328 */ ULong guest_f22;
      /*  336 */ ULong guest_f23;
      /*  344 */ ULong guest_f24;
      /*  352 */ ULong guest_f25;
      /*  360 */ ULong guest_f26;
      /*  368 */ ULong guest_f27;
      /*  376 */ ULong guest_f28;
      /*  384 */ ULong guest_f29;
      /*  392 */ ULong guest_f30;
      /*  400 */ ULong guest_f31;

      /*  408 */ UInt guest_FIR;
      /*  412 */ UInt guest_FCCR;
      /*  416 */ UInt guest_FEXR;
      /*  420 */ UInt guest_FENR;
      /*  424 */ UInt guest_FCSR;

      /* TLS pointer for the thread. It's read-only in user space.
         On Linux it is set in user space by various thread-related
         syscalls.
         User Local Register.
         This register provides read access to the coprocessor 0
         UserLocal register, if it is implemented. In some operating
         environments, the UserLocal register is a pointer to a
         thread-specific storage block.
      */
      /*  428 */ UInt guest_ULR;

      /* Emulation notes */
      /*  432 */ UInt guest_EMNOTE;

      /* For clflush: record start and length of area to invalidate. */
      /*  436 */ UInt guest_CMSTART;
      /*  440 */ UInt guest_CMLEN;
      /*  444 */ UInt guest_NRADDR;

      /*  448 */ UInt guest_COND;

      /* MIPS32 DSP ASE(r2) specific registers. */
      /*  452 */ UInt guest_DSPControl;
      /*  456 */ ULong guest_ac0;
      /*  464 */ ULong guest_ac1;
      /*  472 */ ULong guest_ac2;
      /*  480 */ ULong guest_ac3;

      /*  488 */ UInt guest_CP0_status;
      /*  492 */ UInt guest_CP0_Config5;

      /*  496 */ UInt guest_LLaddr;
      /*  500 */ UInt guest_LLdata;

      /* MIPS32 MSA 128-bit vector registers */
      /*  504 */ V128 guest_w0;
      /*  520 */ V128 guest_w1;
      /*  536 */ V128 guest_w2;
      /*  552 */ V128 guest_w3;
      /*  568 */ V128 guest_w4;
      /*  584 */ V128 guest_w5;
      /*  600 */ V128 guest_w6;
      /*  616 */ V128 guest_w7;
      /*  632 */ V128 guest_w8;
      /*  648 */ V128 guest_w9;
      /*  664 */ V128 guest_w10;
      /*  680 */ V128 guest_w11;
      /*  696 */ V128 guest_w12;
      /*  712 */ V128 guest_w13;
      /*  728 */ V128 guest_w14;
      /*  744 */ V128 guest_w15;
      /*  760 */ V128 guest_w16;
      /*  776 */ V128 guest_w17;
      /*  792 */ V128 guest_w18;
      /*  808 */ V128 guest_w19;
      /*  824 */ V128 guest_w20;
      /*  840 */ V128 guest_w21;
      /*  856 */ V128 guest_w22;
      /*  872 */ V128 guest_w23;
      /*  888 */ V128 guest_w24;
      /*  904 */ V128 guest_w25;
      /*  920 */ V128 guest_w26;
      /*  936 */ V128 guest_w27;
      /*  952 */ V128 guest_w28;
      /*  968 */ V128 guest_w29;
      /*  984 */ V128 guest_w30;
      /*  1000 */ V128 guest_w31;

      /*  1016 */ UInt guest_MSACSR;

      /*  1020 */ UInt _padding3;
} VexGuestMIPS32State;"""



MIPS64 = """
typedef
   struct {
      /*    0 */ ULong host_EvC_FAILADDR;
      /*    8 */ UInt host_EvC_COUNTER;
      /*   12 */ UInt _padding1;

      /* CPU Registers */
      /*   16 */ ULong guest_r0;   /* Hardwired to 0. */
      /*   24 */ ULong guest_r1;   /* Assembler temporary */
      /*   32 */ ULong guest_r2;   /* Values for function returns ...*/
      /*   40 */ ULong guest_r3;   /* ... and expression evaluation */
      /*   48 */ ULong guest_r4;   /* Function arguments */
      /*   56 */ ULong guest_r5;
      /*   64 */ ULong guest_r6;
      /*   72 */ ULong guest_r7;
      /*   80 */ ULong guest_r8;
      /*   88 */ ULong guest_r9;
      /*   96 */ ULong guest_r10;
      /*  104 */ ULong guest_r11;
      /*  112 */ ULong guest_r12;  /* Temporaries */
      /*  120 */ ULong guest_r13;
      /*  128 */ ULong guest_r14;
      /*  136 */ ULong guest_r15;
      /*  144 */ ULong guest_r16;  /* Saved temporaries */
      /*  152 */ ULong guest_r17;
      /*  160 */ ULong guest_r18;
      /*  168 */ ULong guest_r19;
      /*  176 */ ULong guest_r20;
      /*  184 */ ULong guest_r21;
      /*  192 */ ULong guest_r22;
      /*  200 */ ULong guest_r23;
      /*  208 */ ULong guest_r24;  /* Temporaries */
      /*  216 */ ULong guest_r25;
      /*  224 */ ULong guest_r26;  /* Reserved for OS kernel */
      /*  232 */ ULong guest_r27;
      /*  240 */ ULong guest_r28;  /* Global pointer */
      /*  248 */ ULong guest_r29;  /* Stack pointer */
      /*  256 */ ULong guest_r30;  /* Frame pointer */
      /*  264 */ ULong guest_r31;  /* Return address */
      /*  272 */ ULong guest_PC;   /* Program counter */
      /*  280 */ ULong guest_HI;   /* Multiply and divide reg higher result */
      /*  288 */ ULong guest_LO;   /* Multiply and divide reg lower result */

      /* FPU Registers */
      /*  296 */ ULong guest_f0;   /* Floating point gen. purpose registers */
      /*  304 */ ULong guest_f1;
      /*  312 */ ULong guest_f2;
      /*  320 */ ULong guest_f3;
      /*  328 */ ULong guest_f4;
      /*  336 */ ULong guest_f5;
      /*  344 */ ULong guest_f6;
      /*  352 */ ULong guest_f7;
      /*  360 */ ULong guest_f8;
      /*  368 */ ULong guest_f9;
      /*  376 */ ULong guest_f10;
      /*  384 */ ULong guest_f11;
      /*  392 */ ULong guest_f12;
      /*  400 */ ULong guest_f13;
      /*  408 */ ULong guest_f14;
      /*  416 */ ULong guest_f15;
      /*  424 */ ULong guest_f16;
      /*  432 */ ULong guest_f17;
      /*  440 */ ULong guest_f18;
      /*  448 */ ULong guest_f19;
      /*  456 */ ULong guest_f20;
      /*  464 */ ULong guest_f21;
      /*  472 */ ULong guest_f22;
      /*  480 */ ULong guest_f23;
      /*  488 */ ULong guest_f24;
      /*  496 */ ULong guest_f25;
      /*  504 */ ULong guest_f26;
      /*  512 */ ULong guest_f27;
      /*  520 */ ULong guest_f28;
      /*  528 */ ULong guest_f29;
      /*  536 */ ULong guest_f30;
      /*  544 */ ULong guest_f31;

      /*  552 */ UInt guest_FIR;
      /*  556 */ UInt guest_FCCR;
      /*  560 */ UInt guest_FEXR;
      /*  564 */ UInt guest_FENR;
      /*  568 */ UInt guest_FCSR;
      /*  572 */ UInt guest_CP0_status;

      /* TLS pointer for the thread. It's read-only in user space. On Linux it
         is set in user space by various thread-related syscalls.
         User Local Register.
         This register provides read access to the coprocessor 0
         UserLocal register, if it is implemented. In some operating
         environments, the UserLocal register is a pointer to a thread-specific
         storage block.
      */
      /*  576 */ ULong guest_ULR;

      /* Emulation notes */
      /*  584 */ UInt guest_EMNOTE;
      /*  588 */ UInt guest_COND;

      /* For clflush: record start and length of area to invalidate */
      /*  592 */ ULong guest_CMSTART;
      /*  600 */ ULong guest_CMLEN;

      /*  608 */ ULong guest_NRADDR;

      /*  616 */ ULong guest_LLaddr;
      /*  624 */ ULong guest_LLdata;

      /* MIPS32 MSA 128-bit vector registers */
      /*  632 */ V128 guest_w0;
      /*  648 */ V128 guest_w1;
      /*  664 */ V128 guest_w2;
      /*  680 */ V128 guest_w3;
      /*  696 */ V128 guest_w4;
      /*  712 */ V128 guest_w5;
      /*  728 */ V128 guest_w6;
      /*  744 */ V128 guest_w7;
      /*  760 */ V128 guest_w8;
      /*  776 */ V128 guest_w9;
      /*  792 */ V128 guest_w10;
      /*  808 */ V128 guest_w11;
      /*  824 */ V128 guest_w12;
      /*  840 */ V128 guest_w13;
      /*  856 */ V128 guest_w14;
      /*  872 */ V128 guest_w15;
      /*  888 */ V128 guest_w16;
      /*  904 */ V128 guest_w17;
      /*  920 */ V128 guest_w18;
      /*  936 */ V128 guest_w19;
      /*  952 */ V128 guest_w20;
      /*  968 */ V128 guest_w21;
      /*  984 */ V128 guest_w22;
      /* 1000 */ V128 guest_w23;
      /* 1016 */ V128 guest_w24;
      /* 1032 */ V128 guest_w25;
      /* 1048 */ V128 guest_w26;
      /* 1064 */ V128 guest_w27;
      /* 1080 */ V128 guest_w28;
      /* 1096 */ V128 guest_w29;
      /* 1112 */ V128 guest_w30;
      /* 1128 */ V128 guest_w31;
      /* 1144 */ UInt guest_MSACSR;

      /* 1148 */ UInt _padding2;

} VexGuestMIPS64State;"""


S390X = """
typedef struct {

/*------------------------------------------------------------*/
/*--- ar registers                                         ---*/
/*------------------------------------------------------------*/

   /*    0 */  UInt guest_a0;
   /*    4 */  UInt guest_a1;
   /*    8 */  UInt guest_a2;
   /*   12 */  UInt guest_a3;
   /*   16 */  UInt guest_a4;
   /*   20 */  UInt guest_a5;
   /*   24 */  UInt guest_a6;
   /*   28 */  UInt guest_a7;
   /*   32 */  UInt guest_a8;
   /*   36 */  UInt guest_a9;
   /*   40 */  UInt guest_a10;
   /*   44 */  UInt guest_a11;
   /*   48 */  UInt guest_a12;
   /*   52 */  UInt guest_a13;
   /*   56 */  UInt guest_a14;
   /*   60 */  UInt guest_a15;

/*------------------------------------------------------------*/
/*--- fpr & vr registers                                   ---*/
/*------------------------------------------------------------*/

   /*
      FPRs[0-15] are mapped to the first double words of VR's[0-15].
      According to documentation if we modify fpr1 with FP insn then the content of vr1's 64..128
      bits is unpredictable. If we modify 64..128 of vr1 then fpr1's value is unpredictable too.
      In our implementation writing to one half of vr doesn't affect another part but
      apllications shouldn't rely on it.
   */

   /*   64 */  V128 guest_v0;
   /*   80 */  V128 guest_v1;
   /*   96 */  V128 guest_v2;
   /*  112 */  V128 guest_v3;
   /*  128 */  V128 guest_v4;
   /*  144 */  V128 guest_v5;
   /*  160 */  V128 guest_v6;
   /*  176 */  V128 guest_v7;
   /*  192 */  V128 guest_v8;
   /*  208 */  V128 guest_v9;
   /*  224 */  V128 guest_v10;
   /*  240 */  V128 guest_v11;
   /*  256 */  V128 guest_v12;
   /*  272 */  V128 guest_v13;
   /*  288 */  V128 guest_v14;
   /*  304 */  V128 guest_v15;
   /*  320 */  V128 guest_v16;
   /*  336 */  V128 guest_v17;
   /*  352 */  V128 guest_v18;
   /*  368 */  V128 guest_v19;
   /*  384 */  V128 guest_v20;
   /*  400 */  V128 guest_v21;
   /*  416 */  V128 guest_v22;
   /*  432 */  V128 guest_v23;
   /*  448 */  V128 guest_v24;
   /*  464 */  V128 guest_v25;
   /*  480 */  V128 guest_v26;
   /*  496 */  V128 guest_v27;
   /*  512 */  V128 guest_v28;
   /*  528 */  V128 guest_v29;
   /*  544 */  V128 guest_v30;
   /*  560 */  V128 guest_v31;

/*------------------------------------------------------------*/
/*--- gpr registers                                        ---*/
/*------------------------------------------------------------*/

   /*  568 */  ULong guest_r0;
   /*  576 */  ULong guest_r1;
   /*  584 */  ULong guest_r2;
   /*  592 */  ULong guest_r3;
   /*  600 */  ULong guest_r4;
   /*  608 */  ULong guest_r5;
   /*  616 */  ULong guest_r6;
   /*  624 */  ULong guest_r7;
   /*  632 */  ULong guest_r8;
   /*  640 */  ULong guest_r9;
   /*  648 */  ULong guest_r10;
   /*  656 */  ULong guest_r11;
   /*  664 */  ULong guest_r12;
   /*  672 */  ULong guest_r13;
   /*  680 */  ULong guest_r14;
   /*  688 */  ULong guest_r15;

/*------------------------------------------------------------*/
/*--- S390 miscellaneous registers                         ---*/
/*------------------------------------------------------------*/

   /*  696 */  ULong guest_counter;
   /*  704 */  UInt guest_fpc;
   /*  708 */  UChar unused[4]; /* 4-byte hole to get 8-byte alignment */
   /*  712 */  ULong guest_IA;

/*------------------------------------------------------------*/
/*--- S390 pseudo registers                                ---*/
/*------------------------------------------------------------*/

   /*  720 */  ULong guest_SYSNO;

/*------------------------------------------------------------*/
/*--- 4-word thunk used to calculate the condition code    ---*/
/*------------------------------------------------------------*/

   /*  728 */  ULong guest_CC_OP;
   /*  736 */  ULong guest_CC_DEP1;
   /*  744 */  ULong guest_CC_DEP2;
   /*  752 */  ULong guest_CC_NDEP;

/*------------------------------------------------------------*/
/*--- Pseudo registers. Required by all architectures      ---*/
/*------------------------------------------------------------*/

   /* See comments at bottom of libvex.h */
   /*  760 */  ULong guest_NRADDR;
   /*  768 */  ULong guest_CMSTART;
   /*  776 */  ULong guest_CMLEN;

   /* Used when backing up to restart a syscall that has
      been interrupted by a signal. See also comment in
      libvex_ir.h */
   /*  784 */  ULong guest_IP_AT_SYSCALL;

   /* Emulation notes; see comments in libvex_emnote.h */
   /*  792 */  UInt guest_EMNOTE;

   /* For translation chaining */
   /*  796 */  UInt  host_EvC_COUNTER;
   /*  800 */  ULong host_EvC_FAILADDR;

/*------------------------------------------------------------*/
/*--- Force alignment to 16 bytes                          ---*/
/*------------------------------------------------------------*/
   /*  808 */  UChar padding[0];

   /*  816 */  /* This is the size of the guest state */
} VexGuestS390XState;"""



AMD64 = """
typedef
   struct {
      /* Event check fail addr, counter, and padding to make RAX 16
         aligned. */
      /*   0 */ ULong  host_EvC_FAILADDR;
      /*   8 */ UInt   host_EvC_COUNTER;
      /*  12 */ UInt   pad0;
      /*  16 */ ULong  guest_RAX;
      /*  24 */ ULong  guest_RCX;
      /*  32 */ ULong  guest_RDX;
      /*  40 */ ULong  guest_RBX;
      /*  48 */ ULong  guest_RSP;
      /*  56 */ ULong  guest_RBP;
      /*  64 */ ULong  guest_RSI;
      /*  72 */ ULong  guest_RDI;
      /*  80 */ ULong  guest_R8;
      /*  88 */ ULong  guest_R9;
      /*  96 */ ULong  guest_R10;
      /* 104 */ ULong  guest_R11;
      /* 112 */ ULong  guest_R12;
      /* 120 */ ULong  guest_R13;
      /* 128 */ ULong  guest_R14;
      /* 136 */ ULong  guest_R15;
      /* 4-word thunk used to calculate O S Z A C P flags. */
      /* 144 */ ULong  guest_CC_OP;
      /* 152 */ ULong  guest_CC_DEP1;
      /* 160 */ ULong  guest_CC_DEP2;
      /* 168 */ ULong  guest_CC_NDEP;
      /* The D flag is stored here, encoded as either -1 or +1 */
      /* 176 */ ULong  guest_DFLAG;
      /* 184 */ ULong  guest_RIP;
      /* Bit 18 (AC) of eflags stored here, as either 0 or 1. */
      /* ... */ ULong  guest_ACFLAG;
      /* Bit 21 (ID) of eflags stored here, as either 0 or 1. */
      /* 192 */ ULong guest_IDFLAG;
      /* Probably a lot more stuff too. 
         D,ID flags
         16  128-bit SSE registers
         all the old x87 FPU gunk
         segment registers */

      /* HACK to e.g. make tls on amd64-linux/solaris work.  %fs only ever seems
         to hold a constant value (zero on linux main thread, 0x63 in other
         threads), and so guest_FS_CONST holds
         the 64-bit offset associated with this constant %fs value. */
      /* 200 */ ULong guest_FS_CONST;

      /* YMM registers.  Note that these must be allocated
         consecutively in order that the SSE4.2 PCMP{E,I}STR{I,M}
         helpers can treat them as an array.  YMM16 is a fake reg used
         as an intermediary in handling aforementioned insns. */
      /* 208 */ULong guest_SSEROUND;
      /* 216 */U256  guest_YMM0;
      U256  guest_YMM1;
      U256  guest_YMM2;
      U256  guest_YMM3;
      U256  guest_YMM4;
      U256  guest_YMM5;
      U256  guest_YMM6;
      U256  guest_YMM7;
      U256  guest_YMM8;
      U256  guest_YMM9;
      U256  guest_YMM10;
      U256  guest_YMM11;
      U256  guest_YMM12;
      U256  guest_YMM13;
      U256  guest_YMM14;
      U256  guest_YMM15;
      U256  guest_YMM16;

      /* FPU */
      /* Note.  Setting guest_FTOP to be ULong messes up the
         delicately-balanced PutI/GetI optimisation machinery.
         Therefore best to leave it as a UInt. */
      UInt  guest_FTOP;
      UInt  pad1;
      ULong guest_FPREG[8];
      UChar guest_FPTAG[8];
      ULong guest_FPROUND;
      ULong guest_FC3210;

      /* Emulation notes */
      UInt  guest_EMNOTE;
      UInt  pad2;

      /* Translation-invalidation area description.  Not used on amd64
         (there is no invalidate-icache insn), but needed so as to
         allow users of the library to uniformly assume that the guest
         state contains these two fields -- otherwise there is
         compilation breakage.  On amd64, these two fields are set to
         zero by LibVEX_GuestAMD64_initialise and then should be
         ignored forever thereafter. */
      ULong guest_CMSTART;
      ULong guest_CMLEN;

      /* Used to record the unredirected guest address at the start of
         a translation whose start has been redirected.  By reading
         this pseudo-register shortly afterwards, the translation can
         find out what the corresponding no-redirection address was.
         Note, this is only set for wrap-style redirects, not for
         replace-style ones. */
      ULong guest_NRADDR;

      /* Used for Darwin syscall dispatching. */
      ULong guest_SC_CLASS;

      /* HACK to make e.g. tls on darwin work, wine on linux work, ...
         %gs only ever seems to hold a constant value (e.g. 0x60 on darwin,
         0x6b on linux), and so guest_GS_CONST holds the 64-bit offset
         associated with this constant %gs value.  (A direct analogue
         of the %fs-const hack for amd64-linux/solaris). */
      ULong guest_GS_CONST;

      /* Needed for Darwin (but mandated for all guest architectures):
         RIP at the last syscall insn (int 0x80/81/82, sysenter,
         syscall).  Used when backing up to restart a syscall that has
         been interrupted by a signal. */
      ULong guest_IP_AT_SYSCALL;

      /* Padding to make it have an 16-aligned size */
      ULong pad3;
   }
   VexGuestAMD64State;
"""




stmp = """#define ARM_REGS_offset_DEF(REGNAME) REGNAME = offsetof(VexGuestARMState, guest_##REGNAME)
#define ARM_REGS_size_DEF(REGNAME) REGNAME = sizeof(VexGuestARMState::guest_##REGNAME)
#define ARM_ALL_REGS_DEF(_macro) \\\n{:}"""


import re
import os

archs = ["X86", "AMD64", "ARM", "ARM64", "PPC32", "PPC64", "S390X", "MIPS32", "MIPS64"]
for arch in archs:
    state_layout = globals()[arch]
    # print(state_layout)
    tmp = ""
    for li in state_layout.split("\n"):
        regex = re.match(r'[^|]*guest_(?P<reg>[A-Za-z0-9_]+)[^;]*;', li)
        if regex:
            reg = regex.groupdict()["reg"]
            tmp += "_macro(%s),\\\n"%reg
    res = stmp.replace("ARM", arch).format(tmp)[:-3]+"\n\n"
    print(res)


































