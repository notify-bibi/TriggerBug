#ifndef ARCH_H
#define ARCH_H
extern "C" {
#include "libvex.h"
}
namespace Arch {
	using Arch = VexArch;

static inline Arch getHostArch(void)
{
	#if defined(__amd64__)
		return VexArchAMD64;
	#elif defined(__i386__)
		return VexArchX86;
	#elif defined(__arm__)
		return ARM;
	#else
		#error Unsupported Host Architecture
	#endif
}
}
#undef True
#undef False
#endif
