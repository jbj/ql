#define _In_
#define _Out_
#define _Check_return_

// These definitions are included in some versions of sal.h. They interfere
// with the C++11 `override` annotation.
#define __inner_override
#define override __inner_override

#define __SAL_VERSION 20
