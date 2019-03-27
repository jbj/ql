# Improvements to C/C++ analysis

## General improvements

## New queries

| **Query**                   | **Tags**  | **Purpose**                                                        |
|-----------------------------|-----------|--------------------------------------------------------------------|
| Call to alloca in a loop (`cpp/alloca-in-loop`) | reliability, correctness, external/cwe/cwe-770 | Finds calls to `alloca` in loops, which can lead to stack overflow if the number of iterations is large.  Newly displayed on LGTM. |

## Changes to existing queries

| **Query**                  | **Expected impact**    | **Change**                                                       |
|----------------------------|------------------------|------------------------------------------------------------------|
| Mismatching new/free or malloc/delete (`cpp/new-free-mismatch`) | Fewer false positive results | Fixed an issue where functions were being identified as allocation functions inappropriately.  Also affects `cpp/new-array-delete-mismatch` and `cpp/new-delete-array-mismatch`. |
| Resource not released in destructor (`cpp/resource-not-released-in-destructor`) | Fewer false positive results | Resource allocation and deallocation functions are now determined more accurately. |

## Changes to QL libraries
