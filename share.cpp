#include <limits.h>
SCHAR_MAX

//void clang_analyzer_printState();
//void leak(int** p) {
//	int v = 120;
//	int kkkkkk = 122;
//	// clang_analyzer_printState();
//	p[0] = &v + kkkkkk;
//	// clang_analyzer_printState();
//}
//void entry1(int a) {
//	int* p1 = nullptr;
//	int* p2;
//	if (a == 0)
//		leak(&p1 + 1 - 1);
//	else 
//		leak(nullptr);
//	p2 = p1;
//}
//void func(int a) { entry1(0); };
//

//
//void entry2() {
//	int* p2;
//	leak(&p2);
//}
//
//#include <stdio.h>
//#include <string.h>
//void test(char *log, unsigned int len) {
//	char buf[32] = {0};
//	if (len < 32) {
//		strlen(log);
//		strncpy(buf, log, len);
//	}
//
//}
//void test2(char* log, unsigned int len) {
//	char buf[2] =  "1";
//	buf[1] = '1';
//	clang_analyzer_printState();
//	test(buf, len);
//}

//
//#include <string.h>
//
//enum { STR_SIZE = 32 };
//
//size_t func(const char* source) {
//	char c_str[STR_SIZE];
//	size_t ret = 0;
//
//	if (source) {
//		ret = strlen(source);
//	}
//	else {
//		/* Handle null pointer */
//	}
//	return ret;
//}
//struct MyStruct
//{
//	const char* source;
//}G;
//
//size_t entry() {
//	char v[20];
//	// G.source = v;
//	func(G.source);
//}