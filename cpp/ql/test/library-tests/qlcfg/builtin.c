
int builtin(int x, int y) {
  return __builtin_choose_expr(0, x, y);
}
