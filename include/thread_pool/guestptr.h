#ifndef GUESTPTR_H
#define GUESTPTR_H

#include <stdint.h>

/* class to enforce proper use of guest ptrs, operators
   are defined as need to make code look nicer */
class guest_ptr
{
public:
	guest_ptr() : o(0) {}
	explicit guest_ptr(uintptr_t a) : o(a) {}
	uintptr_t o;
	operator uintptr_t() const { return o; }
};

template <typename T> 
guest_ptr operator+(const guest_ptr& g, T offset) {
	return guest_ptr(g.o + offset);
}
inline uintptr_t operator-(const guest_ptr& g, guest_ptr h) {
	return g.o - h.o;
}
inline bool operator < (const guest_ptr& g, guest_ptr h) {
	return g.o < h.o;
}
inline bool operator > (const guest_ptr& g, guest_ptr h) {
	return g.o > h.o;
}

inline bool operator == (const guest_ptr& g, guest_ptr h) {
	return g.o == h.o;
}
#include <utility>
typedef std::pair<guest_ptr, uint8_t>	InstExtent;

#endif
