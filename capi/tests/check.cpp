// b3.h from C++: it compiles as C++11 with every warning on, and a hasher
// initializes (tests/c.rs builds and runs it).
#include "b3.h"
int main() { b3_hasher h; b3_mode m = b3_plain(); b3_hasher_init(&h, &m); return 0; }
