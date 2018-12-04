// semmle-extractor-options: --clang

#define vector(elcount, type)  __attribute__((vector_size((elcount)*sizeof(type)))) type

int builtin(int x, int y) {
  int acc;

  acc += __builtin_choose_expr(0, x+0, y);

  __builtin_assume(x != 42);

  acc += (int)__builtin_readcyclecounter();

  vector(4, int) vec = { 0, 1, 2, 3 };
  vector(4, int) vec2 = __builtin_shufflevector(vec, vec, 3+0, 2, 1, 0);

  // Clang extension causes trap import errors
  //(void)__builtin_convertvector(vec, short __attribute__((__vector_size__(8))));

  acc += __builtin_bitreverse32(x+0);
  acc += __builtin_rotateleft32(x+1, y);
  acc += __builtin_rotateright32(x+1, y);

  if (y == 42) {
	__builtin_unreachable();
  }

  if (__builtin_unpredictable(acc == 1)) {
	return acc;
  }

  return acc;
}
