


extern int printf(char*, ...);

typedef int (*add_t)(int, int);
int add(int a, int b) { return a + b; }

typedef int (*wrapper_t)(add_t, int, int);
int wrapper(int fn(int, int), int a, int b) {
  return fn(a, b);
}

int wrapperWrapper(wrapper_t fn) {
  return fn(&add, 2, 3);
}

int arith(int (*f)(int), int (*g)(int), int x) {
    int (*a)(int) = f;
    int (*b)(int) = f;
    int (*c)(int) = g;
    if ((a != b) || (a == c))
      return -3;

    return f(g(f(x)));
}

typedef int (*arg_t)(int);
int inc(int x) { return x + 1; }
int dbl(int x) { return x * 2; }

struct chooser_struct {
  arg_t inc;
  arg_t dbl;
};
typedef struct chooser_struct chooser_struct;

arg_t chooser(int which) {
  chooser_struct obj = {inc, &dbl};
  arg_t arr[2] = {obj.inc, obj.dbl};
  return arr[which];
}

int fact_impl(int (*fp)(int), int n) {
    return n <= 1 ? 1 : n * fp(n - 1);
}

int fact(int n) {
    int (*fp)(int) = fact;
    return fact_impl(fp, n);
}

int main(void) {
  int (*printf_ptr) (char*, ...) = 0;
  if(printf_ptr)
    return -1;
  printf_ptr = printf;
  if(!printf_ptr)
    return -2;

  add_t add_ptr = &add;
  
  printf_ptr("Result: %d\n", (*add_ptr)(2, 3));
  printf_ptr("ResultWrapper: %d\n", wrapper(add, 2, 3));
  printf_ptr("ResultWrapperWrapper: %d\n", wrapperWrapper(&wrapper));
  printf_ptr("ResultArith: %d\n", arith(inc, dbl, 1));
  printf_ptr("ResultChooser: %d\n", arith(chooser(0), chooser(1), 1));
  printf_ptr("Result 5!: %d\n", fact(5));

  return 0;
}
