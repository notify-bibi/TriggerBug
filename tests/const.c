struct df{
	int a;
	int k;
	int c;
};
int ff(struct df *i, int argn) {
 struct df v = *i;
 int c1 = v.a&0xff;
 int c2 = v.c;
 int c3 = c1 + c2;
 ((char*)&v.c)[1] = c3;
 *i = v;
 return c3;
}
// int ff(int argn) {
 
 // int c1 = argn;
 // int c2 = 8;
 // int c3 = c1 + c2;
 // return c3;
// }