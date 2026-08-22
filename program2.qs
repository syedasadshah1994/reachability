namespace QPNReachability {
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Diagnostics;

    operation EncodeCount(place : Qubit[], count : Int) : Unit {
        // MSB-LSB: place[0]=MSB, place[1]=LSB
        if ((count &&& 2) != 0) { X(place[0]); }
        if ((count &&& 1) != 0) { X(place[1]); }
    }

    operation ControlledIncrement(ctrl : Qubit, place : Qubit[]) : Unit {
        Controlled X([ctrl, place[1]], place[0]);
        Controlled X([ctrl], place[1]);
    }

    operation ControlledDecrement(ctrl : Qubit, place : Qubit[]) : Unit {
        Controlled X([ctrl], place[1]);
        Controlled X([ctrl, place[1]], place[0]);
    }

    operation ComputeNonZero(place : Qubit[], flag : Qubit) : Unit {
        CNOT(place[0], flag);
        CNOT(place[1], flag);
        CCNOT(place[0], place[1], flag);
    }

    operation ComputeAlpha01(alpha : Qubit[], flag : Qubit) : Unit {
        within { X(alpha[0]); }
        apply { CCNOT(alpha[0], alpha[1], flag); }
    }

    operation ComputeAlpha10(alpha : Qubit[], flag : Qubit) : Unit {
        within { X(alpha[1]); }
        apply { CCNOT(alpha[0], alpha[1], flag); }
    }

    operation ComputeAlpha11(alpha : Qubit[], flag : Qubit) : Unit {
        CCNOT(alpha[0], alpha[1], flag);
    }

    operation ComputeFired01(fired : Qubit[], flag : Qubit) : Unit {
        within { X(fired[0]); }
        apply { CCNOT(fired[0], fired[1], flag); }
    }

    operation ComputeFired10(fired : Qubit[], flag : Qubit) : Unit {
        within { X(fired[1]); }
        apply { CCNOT(fired[0], fired[1], flag); }
    }

    operation ComputeFired11(fired : Qubit[], flag : Qubit) : Unit {
        CCNOT(fired[0], fired[1], flag);
    }

    operation UT(marking : Qubit[], alpha : Qubit[], fired : Qubit[]) : Unit {

        let p1 = marking[0..1];
        let p2 = marking[2..3];
        let p3 = marking[4..5];
        let p4 = marking[6..7];
        let p5 = marking[8..9];

        use nz = Qubit[3];
        use a = Qubit[3];
        use cond = Qubit[3];

        ComputeNonZero(p1, nz[0]);
        ComputeNonZero(p2, nz[1]);
        ComputeNonZero(p3, nz[2]);

        ComputeAlpha01(alpha, a[0]);
        ComputeAlpha10(alpha, a[1]);
        ComputeAlpha11(alpha, a[2]);

        Controlled X([a[0], nz[0], nz[1]], cond[0]);
        CCNOT(a[1], nz[2], cond[1]);
        CCNOT(a[2], nz[2], cond[2]);

        // fired encoding:
        // 00 = none
        // 01 = T1
        // 10 = T2
        // 11 = T3

        Controlled X([cond[0]], fired[1]);
        Controlled X([cond[1]], fired[0]);
        Controlled X([cond[2]], fired[0]);
        Controlled X([cond[2]], fired[1]);

        CCNOT(a[2], nz[2], cond[2]);
        CCNOT(a[1], nz[2], cond[1]);
        Controlled X([a[0], nz[0], nz[1]], cond[0]);

        ComputeAlpha11(alpha, a[2]);
        ComputeAlpha10(alpha, a[1]);
        ComputeAlpha01(alpha, a[0]);

        ComputeNonZero(p3, nz[2]);
        ComputeNonZero(p2, nz[1]);
        ComputeNonZero(p1, nz[0]);

        use isT1 = Qubit();
        use isT2 = Qubit();
        use isT3 = Qubit();

        // T1: P1 + P2 -> 2P3
        ComputeFired01(fired, isT1);
        ControlledDecrement(isT1, p1);
        ControlledDecrement(isT1, p2);
        ControlledIncrement(isT1, p3);
        ControlledIncrement(isT1, p3);
        ComputeFired01(fired, isT1);

        // T2: P3 -> P4
        ComputeFired10(fired, isT2);
        ControlledDecrement(isT2, p3);
        ControlledIncrement(isT2, p4);
        ComputeFired10(fired, isT2);

        // T3: P3 -> P5
        ComputeFired11(fired, isT3);
        ControlledDecrement(isT3, p3);
        ControlledIncrement(isT3, p5);
        ComputeFired11(fired, isT3);
    }

    @EntryPoint()
    operation Main() : Unit {

        use marking = Qubit[10];

        let p1 = marking[0..1];
        let p2 = marking[2..3];
        let p3 = marking[4..5];
        let p4 = marking[6..7];
        let p5 = marking[8..9];

        use alpha1 = Qubit[2];
        use alpha2 = Qubit[2];
        use alpha3 = Qubit[2];

        use fired1 = Qubit[2];
        use fired2 = Qubit[2];
        use fired3 = Qubit[2];

        EncodeCount(p1, 2);
        EncodeCount(p2, 1);
        EncodeCount(p3, 0);
        EncodeCount(p4, 0);
        EncodeCount(p5, 0);

        Message("Initial marking:");
        Message("Expected marking bits: 1001000000");
        DumpRegister( marking);

        // First iteration
        H(alpha1[0]);
        H(alpha1[1]);

        Message("After superposing alpha1:");
        DumpRegister( marking + alpha1);

        UT(marking, alpha1, fired1);

        Message("After first iteration:");
        Message("Register order: marking + alpha1 + fired1");
        DumpRegister( marking + alpha1 + fired1);

        // Second iteration
        H(alpha2[0]);
        H(alpha2[1]);

        Message("After superposing alpha2:");
        Message("Register order: marking + alpha1 + fired1 + alpha2");
        DumpRegister( marking + alpha1 + fired1 + alpha2);

        UT(marking, alpha2, fired2);

        Message("After second iteration:");
        Message("Register order: marking + alpha1 + fired1 + alpha2 + fired2");
        DumpRegister( marking + alpha1 + fired1 + alpha2 + fired2);

        // Third iteration
        H(alpha3[0]);
        H(alpha3[1]);

        Message("After superposing alpha3:");
        Message("Register order: marking + alpha1 + fired1 + alpha2 + fired2 + alpha3");
        DumpRegister( marking + alpha1 + fired1 + alpha2 + fired2 + alpha3);

        UT(marking, alpha3, fired3);

        Message("After third iteration:");
        Message("Register order: marking + alpha1 + fired1 + alpha2 + fired2 + alpha3 + fired3");
        DumpRegister( marking + alpha1 + fired1 + alpha2 + fired2 + alpha3 + fired3);

        ResetAll(
            marking
            + alpha1 + alpha2 + alpha3
            + fired1 + fired2 + fired3
        );
    }
}