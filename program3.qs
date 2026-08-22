namespace QPNReachability {
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Diagnostics;

    operation EncodeCount(place : Qubit[], count : Int) : Unit is Adj + Ctl {
        // 2-bit MSB-LSB count encoding:
        // 0 = 00, 1 = 01, 2 = 10, 3 = 11
        if ((count &&& 2) != 0) { X(place[0]); }
        if ((count &&& 1) != 0) { X(place[1]); }
    }

    operation ControlledIncrement(ctrl : Qubit, place : Qubit[]) : Unit is Adj + Ctl {
        // Increment modulo 4.
        Controlled X([ctrl, place[1]], place[0]);
        Controlled X([ctrl], place[1]);
    }

    operation ControlledDecrement(ctrl : Qubit, place : Qubit[]) : Unit is Adj + Ctl {
        // Decrement modulo 4.
        Controlled X([ctrl], place[1]);
        Controlled X([ctrl, place[1]], place[0]);
    }

    operation ComputeNonZero(place : Qubit[], flag : Qubit) : Unit is Adj + Ctl {
        // flag = 1 iff place != 00.
        CNOT(place[0], flag);
        CNOT(place[1], flag);
        CCNOT(place[0], place[1], flag);
    }

    operation ComputeAlpha01(alpha : Qubit[], flag : Qubit) : Unit is Adj + Ctl {
        // alpha = 01.
        within { X(alpha[0]); }
        apply { CCNOT(alpha[0], alpha[1], flag); }
    }

    operation ComputeAlpha10(alpha : Qubit[], flag : Qubit) : Unit is Adj + Ctl {
        // alpha = 10.
        within { X(alpha[1]); }
        apply { CCNOT(alpha[0], alpha[1], flag); }
    }

    operation ComputeAlpha11(alpha : Qubit[], flag : Qubit) : Unit is Adj + Ctl {
        // alpha = 11.
        CCNOT(alpha[0], alpha[1], flag);
    }

    operation ComputeFired01(fired : Qubit[], flag : Qubit) : Unit is Adj + Ctl {
        // fired = 01 means T1 fired.
        within { X(fired[0]); }
        apply { CCNOT(fired[0], fired[1], flag); }
    }

    operation ComputeFired10(fired : Qubit[], flag : Qubit) : Unit is Adj + Ctl {
        // fired = 10 means T2 fired.
        within { X(fired[1]); }
        apply { CCNOT(fired[0], fired[1], flag); }
    }

    operation ComputeFired11(fired : Qubit[], flag : Qubit) : Unit is Adj + Ctl {
        // fired = 11 means T3 fired.
        CCNOT(fired[0], fired[1], flag);
    }

    operation UT(marking : Qubit[], alpha : Qubit[], fired : Qubit[]) : Unit is Adj + Ctl {
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

        // T1: P1 + P2 -> 2P3.
        Controlled X([a[0], nz[0], nz[1]], cond[0]);

        // T2: P3 -> P4.
        CCNOT(a[1], nz[2], cond[1]);

        // T3: P3 -> P5.
        CCNOT(a[2], nz[2], cond[2]);

        // Binary fired encoding:
        // 00 = no transition fired
        // 01 = T1 fired
        // 10 = T2 fired
        // 11 = T3 fired
        Controlled X([cond[0]], fired[1]);
        Controlled X([cond[1]], fired[0]);
        Controlled X([cond[2]], fired[0]);
        Controlled X([cond[2]], fired[1]);

        // Uncompute temporary condition registers.
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

        // T1 update: P1--, P2--, P3 += 2.
        ComputeFired01(fired, isT1);
        ControlledDecrement(isT1, p1);
        ControlledDecrement(isT1, p2);
        ControlledIncrement(isT1, p3);
        ControlledIncrement(isT1, p3);
        ComputeFired01(fired, isT1);

        // T2 update: P3--, P4++.
        ComputeFired10(fired, isT2);
        ControlledDecrement(isT2, p3);
        ControlledIncrement(isT2, p4);
        ComputeFired10(fired, isT2);

        // T3 update: P3--, P5++.
        ComputeFired11(fired, isT3);
        ControlledDecrement(isT3, p3);
        ControlledIncrement(isT3, p5);
        ComputeFired11(fired, isT3);
    }

    operation PhaseI(
        marking : Qubit[],
        alpha1 : Qubit[],
        alpha2 : Qubit[],
        alpha3 : Qubit[],
        fired1 : Qubit[],
        fired2 : Qubit[],
        fired3 : Qubit[]
    ) : Unit is Adj + Ctl {
        let p1 = marking[0..1];
        let p2 = marking[2..3];
        let p3 = marking[4..5];
        let p4 = marking[6..7];
        let p5 = marking[8..9];

        // Initial marking:
        // (P1,P2,P3,P4,P5) = (2,1,0,0,0)
        // bits = 10 01 00 00 00 = 1001000000
        // decimal = 576
        EncodeCount(p1, 2);
        EncodeCount(p2, 1);
        EncodeCount(p3, 0);
        EncodeCount(p4, 0);
        EncodeCount(p5, 0);

        H(alpha1[0]);
        H(alpha1[1]);
        UT(marking, alpha1, fired1);

        H(alpha2[0]);
        H(alpha2[1]);
        UT(marking, alpha2, fired2);

        H(alpha3[0]);
        H(alpha3[1]);
        UT(marking, alpha3, fired3);
    }

    operation OracleTargetMarking(marking : Qubit[], target : Int) : Unit is Adj + Ctl {
        // Dynamic oracle.
        // marking has 10 qubits in MSB-first order.
        // target is the decimal value of the target marking.
        //
        // Example:
        // target = 288 means bits 0100100000 = (1,0,2,0,0)
        // target = 261 means bits 0100000101 = (1,0,0,1,1)

        let weights = [512, 256, 128, 64, 32, 16, 8, 4, 2, 1];

        within {
            for i in 0..9 {
                if ((target &&& weights[i]) == 0) {
                    X(marking[i]);
                }
            }
        } apply {
            H(marking[9]);
            Controlled X(marking[0..8], marking[9]);
            H(marking[9]);
        }
    }

    operation ReflectionAboutZero(register : Qubit[]) : Unit is Adj + Ctl {
        let n = Length(register);

        within {
            for q in register {
                X(q);
            }
        } apply {
            H(register[n - 1]);
            Controlled X(register[0..n - 2], register[n - 1]);
            H(register[n - 1]);
        }
    }

    operation GroverIteration(
        marking : Qubit[],
        alpha1 : Qubit[],
        alpha2 : Qubit[],
        alpha3 : Qubit[],
        fired1 : Qubit[],
        fired2 : Qubit[],
        fired3 : Qubit[],
        target : Int
    ) : Unit {
        let allRegs =
            marking
            + alpha1 + fired1
            + alpha2 + fired2
            + alpha3 + fired3;

        OracleTargetMarking(marking, target);

        Adjoint PhaseI(
            marking,
            alpha1,
            alpha2,
            alpha3,
            fired1,
            fired2,
            fired3
        );

        ReflectionAboutZero(allRegs);

        PhaseI(
            marking,
            alpha1,
            alpha2,
            alpha3,
            fired1,
            fired2,
            fired3
        );
    }

    operation MeasureMarkingAsInt(marking : Qubit[]) : Int {
        mutable value = 0;

        // MSB-first weights for 10-bit marking.
        let weights = [512, 256, 128, 64, 32, 16, 8, 4, 2, 1];

        for i in 0..9 {
            if (M(marking[i]) == One) {
                set value += weights[i];
            }
        }

        return value;
    }

    @EntryPoint()
    operation Main() : Unit {

        

        // Manually set target marking here.
        //
        // 1001000000 = (2,1,0,0,0), decimal 576
        // 0100100000 = (1,0,2,0,0), decimal 288
        // 0100010100 = (1,0,1,1,0), decimal 276
        // 0100010001 = (1,0,1,0,1), decimal 273
        // 0100001000 = (1,0,0,2,0), decimal 264
        // 0100000101 = (1,0,0,1,1), decimal 261
        // 0100000010 = (1,0,0,0,2), decimal 258
        let target = 3;
        // Manually set Grover iterations here.
        let groverIterations = 4;

        mutable count1001000000 = 0; // decimal 576
        mutable count0100100000 = 0; // decimal 288
        mutable count0100010100 = 0; // decimal 276
        mutable count0100010001 = 0; // decimal 273
        mutable count0100001000 = 0; // decimal 264
        mutable count0100000101 = 0; // decimal 261
        mutable count0100000010 = 0; // decimal 258
        mutable other = 0;

        for shot in 1..100 {

            use marking = Qubit[10];

            use alpha1 = Qubit[2];
            use alpha2 = Qubit[2];
            use alpha3 = Qubit[2];

            use fired1 = Qubit[2];
            use fired2 = Qubit[2];
            use fired3 = Qubit[2];

            let allRegs =
                marking
                + alpha1 + fired1
                + alpha2 + fired2
                + alpha3 + fired3;

            PhaseI(
                marking,
                alpha1,
                alpha2,
                alpha3,
                fired1,
                fired2,
                fired3
            );

            for _ in 1..groverIterations {
                GroverIteration(
                    marking,
                    alpha1,
                    alpha2,
                    alpha3,
                    fired1,
                    fired2,
                    fired3,
                    target
                );
            }

            let measured = MeasureMarkingAsInt(marking);

            if (measured == 576) {
                // 1001000000 = (2,1,0,0,0)
                set count1001000000 += 1;
            } elif (measured == 288) {
                // 0100100000 = (1,0,2,0,0)
                set count0100100000 += 1;
            } elif (measured == 276) {
                // 0100010100 = (1,0,1,1,0)
                set count0100010100 += 1;
            } elif (measured == 273) {
                // 0100010001 = (1,0,1,0,1)
                set count0100010001 += 1;
            } elif (measured == 264) {
                // 0100001000 = (1,0,0,2,0)
                set count0100001000 += 1;
            } elif (measured == 261) {
                // 0100000101 = (1,0,0,1,1)
                set count0100000101 += 1;
            } elif (measured == 258) {
                // 0100000010 = (1,0,0,0,2)
                set count0100000010 += 1;
            } else {
                set other += 1;
            }

            ResetAll(allRegs);
        }

        Message($"Grover iterations: {groverIterations}");
        Message($"Target decimal value: {target}");
        Message("Results after 100 shots:");
        Message($"1001000000 = (2,1,0,0,0), decimal 576: {count1001000000}");
        Message($"0100100000 = (1,0,2,0,0), decimal 288: {count0100100000}");
        Message($"0100010100 = (1,0,1,1,0), decimal 276: {count0100010100}");
        Message($"0100010001 = (1,0,1,0,1), decimal 273: {count0100010001}");
        Message($"0100001000 = (1,0,0,2,0), decimal 264: {count0100001000}");
        Message($"0100000101 = (1,0,0,1,1), decimal 261: {count0100000101}");
        Message($"0100000010 = (1,0,0,0,2), decimal 258: {count0100000010}");
        Message($"Other: {other}");
    }
}