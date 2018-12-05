struct PM {
    int x1;
    int x2;
    void f1();
    void f2();
    PM clone();
};

int PM::* getDataMemberPointer(bool);

typedef void (PM::*pmVoidVoid)();
pmVoidVoid getFunctionMemberPointer(bool);

int usePM() {
    int acc;

    PM obj;

    // TODO: These tests don't work on 1.18
    //acc += obj.clone() .* getDataMemberPointer(true);
    //acc += (&obj) ->* getDataMemberPointer(true);

    (obj.clone() .* getFunctionMemberPointer(false))();
    ((&obj) ->* getFunctionMemberPointer(true))();

    return acc;
}
