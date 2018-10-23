#include "sal.h"

class A {
public:
    void method1(_In_ int arg1);
    void method2(_In_ int arg1);
    _Check_return_ char* method3(_Out_ int* arg1);

    int getSALVersion() {
        return __SAL_VERSION;
    }
    void method4(_In_ int arg1);

    void overrideMethod() const override;
    void method5(_In_ int arg1);
};

// BAD: SAL is inconsistent
void A::method1(int arg1){
}

// BAD: SAL is inconsistent
void A::method2(int arg){
}

// GOOD: SAL is consistent
_Check_return_ char* A::method3(_Out_ int* arg1){
}

// GOOD: SAL is consistent
void A::method4(_In_ int arg1){
}

// GOOD: SAL is consistent
void A::method5(_In_ int arg1){
}
