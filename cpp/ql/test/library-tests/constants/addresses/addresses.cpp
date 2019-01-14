// semmle-extractor-options: --c++14

const int int_const = 1;
extern const int extern_int_const = 1;
extern const int extern_int_const_noinit;

int int_var;
int int_arr[4];
int int_arr_arr[4][4];

void sideEffect();
using fptr = void (*)();
using fref = void (&)();



// All variables in this function are initialized to constants, as witnessed by
// the `constexpr` annotation that compiles under C++14.
void constantAddresses(int param) {
    constexpr int *p1 = &int_var;
    constexpr int *p2 = &*&int_var;
    constexpr int *p3 = &int_arr[1] + 1;
    constexpr int (*p4)[4] = &int_arr_arr[1] + 1;
    constexpr int *p5 = &int_arr_arr[1][1] + 1;
    constexpr int *p6 = &int_arr_arr[int_const][extern_int_const];

    // Commented out because clang and EDG disagree on whether this is
    // constant.
    //constexpr int *p7 = &int_arr[ ({ 1; }) ]; // StmtExpr

    constexpr int *p8 = &int_arr[ ((void)0, 1) ]; // CommaExpr
    constexpr int *p9 = &int_arr[int_const ? 1 : param];
    constexpr int *p10 = &int_arr[&int_arr + 1 ? 1 : param]; // recursive
    constexpr int *p11 = &int_arr[&int_arr[1] - &int_arr[0]];

    constexpr int *p12 = p11 + 1;

    constexpr int &r1 = int_var;
    constexpr int &r2 = int_arr_arr[1][1];
    constexpr int &r4 = r2;
    constexpr int &r5 = *(&r2 + 1);

    constexpr fptr fp1 = sideEffect;
    constexpr fptr fp2 = &sideEffect;
    constexpr fptr fp3 = **&**&**sideEffect;

    constexpr fref fr1 = sideEffect;
    constexpr fref fr2 = *&sideEffect;
    constexpr fref fr3 = **sideEffect;
    constexpr fref fr4 = fr1;
}




// All variables in this function are initialized to non-const values. Writing
// `const` in front of any of the variables will be a compile error (C++14).
void nonConstantAddresses(int param, int *pparam, int &rparam, fref frparam) {
    int *p3 = &int_arr[param];
    int *p6 = &int_arr[extern_int_const_noinit];

    int *p7 = &int_arr[ ({ sideEffect(); 1; }) ]; // StmtExpr
    int *p8 = &int_arr[ (sideEffect(), 1) ]; // CommaExpr
    int *p9 = &int_arr[int_const ? param : 1];
    int *p10 = &int_arr[&int_arr + 1 ? param : 1]; // recursive
    int *p12 = pparam;

    int *&&r3 = &int_var; // reference to temporary is not a const
    int &r4 = rparam;

    fref fr4 = frparam;
}
