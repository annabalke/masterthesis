n := 4;
F<a> := GF(2, n);
P<x> := PolynomialRing(F);
Q<y> := quo<P|x^(2^n)+x>;

printf "n=%o\n", n;

function IsPermutation(f, F)
    S := {Evaluate(f, a) : a in F};
    return #S eq #F;
end function;

function DiffUniformity(f, F)
    delta := 0;
    for a in F do
        if a ne 0 then
            diffs := [Evaluate(f, x + a) + Evaluate(f, x) : x in F];
            M := SequenceToMultiset(diffs);
            maxcount := Max([Multiplicity(M, d) : d in Set(diffs)]);
            if maxcount gt delta then
                delta := maxcount;
            end if;
        end if;
    end for;
    return delta;
end function;

function CCZeq2(F1,F2)
    R := Parent(F1);
    F<a> := BaseRing(R);
    n := Degree(F);
    function CF(f)
        M := Matrix(2*n+1, 2^n, 
                    [1: u in F] 
                    cat [Trace(a^i * u): u in F, i in [1..n]] 
                    cat [Trace(a^i * f(u)): u in F, i in [1..n]]);
        return LinearCode(M);
    end function;
    f1 := func<x | Evaluate(F1,x) >;
    f2 := func<x | Evaluate(F2,x) >;
    b, _ := IsIsomorphic(CF(f1), CF(f2));
    return b;
end function;

function IndicatorSetQ(U, n, Q, y)
    if #U eq 0 then
        return Q!0;
    end if;
    prod := Q!1;
    for u in U do
        prod *:= (y + Q!u)^(2^n - 1);
    end for;
    return (Q!1) - prod;
end function;

// Build polynomial in P representing a map F -> F by interpolation
function PolyFromMap(F, P, mapF)
    X := [F | u : u in F];
    Y := [F | mapF(u) : u in F];
    return Interpolation(X, Y);
end function;

// Return subfield K = GF(2,k) inside F = GF(2,2k)
function SubfieldK(F, a, n, k)
    return sub< F | a^((2^n - 1) div (2^k - 1)) >;
end function;

boolList := [];
functions := [];
Tlist := [];

for s in Divisors(n) do
    if s eq n then continue; end if;
    Fs := sub< F | a^((2^n - 1) div (2^s - 1)) >;
    Append(~Tlist, { F!u : u in Fs });
end for;

U := { F!0, F!1 };
Append(~boolList, IndicatorSetQ(U, n, Q, y));

// --------------------------------------------

procedure Gold(n, ~functions)
    printf "\nGold:\n";
    k := n div 2;
    for i in [1..n-1] do
        if not IsEven(n) then
            printf "n is not even\n";
            break;
        end if;
        if IsOdd(k) eq false then
            printf "k must be odd.\n";
            break;
        end if;
        if Gcd(i, n) ne 2 then
            continue;
        end if;
        d := 2^i + 1;
        f := y^d;
        if IsPermutation(f, F) then
            du := DiffUniformity(f, F);
            if du eq 4 then
                //printf "f(x)=%o\n", f;
                if not f in functions then
                    Append(~functions, f);
                end if;
            end if;
        end if;
    end for;
end procedure;

procedure Kasami(n, ~functions)
    printf "\nKasami:\n";
    k := n div 2;
    for i in [1..n-1] do
        if not IsEven(n) then
            printf "n is not even\n";
            break;
        end if;
        if IsOdd(k) eq false then
            printf "k must be odd.\n";
            break;
        end if;
        if Gcd(i, n) ne 2 then
            continue;
        end if;
        d := 2^(2*i) - 2^i + 1;
        f := y^d;
        if IsPermutation(f, F) then
            du := DiffUniformity(f, F);
            if du eq 4 then
                //printf "f(x)= %o\n", f; 
                if not f in functions then
                    Append(~functions, f);
                end if;
            end if;
        end if;
    end for;
end procedure;

procedure InverseFam(n, ~functions)
    printf "\nInverse:\n";
    k := n div 2;
    if not IsEven(n) then
        printf "n is not even\n";
    end if;
    d := 2^n - 2;
    f := y^d;
    if IsPermutation(f, F) then
        du := DiffUniformity(f, F);
        if du eq 4 then
            //printf "f(x)=x^%o\n", d;
            if not f in functions then
                Append(~functions, f);
            end if;
        end if;
    end if;
end procedure;

procedure BrackenLeander(n, ~functions)
    printf "\nBracken-Leander:\n";
    k := (n div 4);
    if not IsEven(n) then
        printf "n is not even\n";
    end if;
    if IsOdd(k) eq false then
        printf "k must be odd.\n";
    end if;
    d := 2^(2*k) + 2^k + 1;
    f := y^d;
    if IsPermutation(f, F) then
        du := DiffUniformity(f, F);
        if du eq 4 then
            //printf "f(x)=x^%o\n", d;
            if not f in functions then
                Append(~functions, f);
            end if;
        end if;
    end if;
end procedure;

procedure BrackenTanTan(n, ~functions)
    printf "\nBracken-Tan-Tan:\n";
    k := n div 3;
    for i in [1..n-1] do
        if not IsEven(n) then
            printf "n must be even\n";
            break;
        end if;
        if not IsEven(k) then
            printf "k must be even.\n";
            break;
        end if;
        if not IsOdd(k div 2) then
            break;
        end if;
        if Gcd(n, i) ne 2 then
            continue;
        end if;
        if (k + i) mod 3 ne 0 then
            continue;
        end if;
        f := (a*y^(2^i + 1)) + (a^(2^k))*(y^(2^(n-k) + 2^(k+i)));
        if IsPermutation(f, F) then
            du := DiffUniformity(f, F);
            if du eq 4 then
                //printf "f(x)= %o\n", f;
                if not f in functions then
                    Append(~functions, f);
                end if;
            end if;
        end if;
    end for;
end procedure;

procedure TanQuTanLi1(n, ~functions)
    printf "\nTanQuTanLi1:\n";
    k := n div 2;
    for i in [1..n-1] do
        if not IsEven(n) then
            printf "n must be even\n";
            break;
        end if;
        f := y^(2^n-2) + (Trace(y + (y^(2^n-2) + 1)^(2^n-2))^(2^i));
        if IsPermutation(f, F) then
            du := DiffUniformity(f, F);
            if du eq 4 then
                //printf "f(x)= %o\n", f;
                if not f in functions then
                    Append(~functions, f);
                end if;
            end if;
        end if;
    end for;
end procedure;

procedure TanQuTanLi2(n, ~functions)
    printf "\nTanQuTanLi2:\n";
    k := n div 2;
    for s in [2..k-1] do
        for i in [1..n-1] do
            f := y^(2^n-2) + (Trace(y^((2^n-4)*2^(s+1)) + (y^(2^n-2) + 1)^(3*2^(s+1)))^(2^i));
            if IsPermutation(f, F) then
                du := DiffUniformity(f, F);
                if du eq 4 then
                    //printf "f(x) = %o\n", f;
                    if not f in functions then
                        Append(~functions, f);
                    end if;
                end if;
            end if;
        end for;
    end for;
end procedure;    

procedure YuWangLi(n,   ~functions)
    printf "\nYuWangLi:\n";
    k := n div 2;
    for i in [0..2^n-3] do
        if not IsOdd(k) then
            printf "k must be odd\n";
            break;
        end if;
        f := y^i;
        if IsPermutation(f, F) then
            du := DiffUniformity(f, F);
            if du eq 4 then
                //printf "f(x)= %o\n", f;
                if not f in functions then
                    Append(~functions, f);
                end if;
            end if;
        end if;
    end for;
end procedure;

procedure ZhaHuSun1(n, ~functions)
    printf "\nZha-Hu-Sun 1:\n";
    for s in [1..n-1] do
        if (n mod s) ne 0 then continue; end if;
        Fs := sub< F | a^((2^n - 1) div (2^s - 1)) >;
        m := s * n;   
        for t in Fs do
            tt := F!t;
            ok := false;

            if (s mod 2 eq 0) and (tt ne 0) then
                ok := true;
            end if;

            if (s in {1,3}) and ((n div 2) mod 2 eq 1) then
                ok := true;
            end if;

            if not ok then continue; end if;

            f := y^(2^n - 2) + tt * (y^(2^s) + y)^(2^m - 1) + tt;
            if IsPermutation(f, F) then
                du := DiffUniformity(f, F);
                if du eq 4 then
                    //printf "f(x) = %o\n", f;
                    if not f in functions then
                        Append(~functions, f);
                    end if;
                end if;
            end if;
        end for;
    end for;
end procedure;


procedure XuCaoXu(n, ~functions)
    printf "\nXuCaoXu:\n";
    for s, k in [1..n-1] do
        if IsOdd(s) and IsOdd(n) and Gcd(k, (s*n)) eq 1 then
            Fs := sub< F | a^((2^n - 1) div (2^s - 1)) >;
            m := s*n;
            for t in Fs do
                tt := F!t;
                f := y^(2^k+1) + tt * (y^(2^s) + y)^(2^(m) - 1);
                if IsPermutation(f, F) then
                    du := DiffUniformity(f, F);
                    if du eq 4 then
                        //printf "f(x)= %o\n", f;
                        if not f in functions then
                            Append(~functions, f);
                        end if;
                    end if;
                end if;
            end for;
        end if; 
    end for;
end procedure;

procedure ZhaHuSun2(n, ~functions)
    printf "\nZha-Hu-Sun 2:\n";
    invQ := y^(2^n - 2);
    oneQ := Q!1;
    for s in [1..n-1] do
        if (n mod s) ne 0 then continue; end if;
        if not IsEven(s) then continue; end if;
        if not IsOdd(n div s) then continue; end if;

        Fs := sub< F | a^( (2^n - 1) div (2^s - 1) ) >;
        Ys_2s := y^(2^s);
        gQ := (Ys_2s + y)^(2^n - 1);
        IsQ := oneQ - gQ; 

        for t1 in Fs do
            if t1 eq 0 then continue; end if;
            if Trace(t1^(-1)) ne 1 then continue; end if;

            for t2 in Fs do
                coeffQ := Q!( (F!t1 - F!1) * invQ + F!t2 );
                fQ := invQ + coeffQ * IsQ;
                f := P!fQ;

                if IsPermutation(f, F) then
                    du := DiffUniformity(f, F);
                    if du eq 4 then
                        //printf "f(x)= %o\n", f;
                        if not f in functions then
                            Append(~functions, f);
                        end if;
                    end if;
                end if;
            end for;
        end for;
    end for;
end procedure;

procedure LiWang1(n, ~functions)
    printf "\nLiWang 1:\n";
    if not n eq 4 then
        printf "n must be 4\n";
    end if;
    coeffs := [
        <F!1, F!1>,
        <a^3, a^9>,
        <a^6, a^3>,
        <a^9, a^12>,
        <a^12, a^6>
    ];
    for pair in coeffs do
        c1 := pair[1];
        c2 := pair[2];
        f := y^(2^n - 2) + c1*y^2 + c2*y^8;
        if IsPermutation(f, F) then
            du := DiffUniformity(f, F);
            if du eq 4 then
                //printf "f(x)= %o\n", f;
                if not f in functions then
                    Append(~functions, f);
                end if;
            end if;
        end if;
    end for;
end procedure;

procedure SinKimKimHan(n, ~functions)
    printf "\nSinKimKimHan:\n";
    inv := y^(2^n - 2);
    for s in [1..n-1] do
        if (n mod s) ne 0 then continue; end if;
        if not IsEven(s) then continue; end if;
        if not IsOdd(n div s) then continue; end if;
        Fs := sub< F | a^((2^n - 1) div (2^s - 1)) >;

        for i in [1..n-1] do
            if (n mod i) ne 0 then continue; end if;
            if not IsOdd(n div i) then continue; end if;
            
            Is := (y^(2^s) + y)^(2^n - 1);
            Ii := (y^(2^i) + y)^(2^n - 1);

            for t in Fs do
                if t eq 0 then continue; end if;   // t in F_q^*
                tt := F!t;
                f := inv + tt*Is + tt*Ii + tt;
                if IsPermutation(f, F) then
                    du := DiffUniformity(f, F);
                    if du eq 4 then
                        //printf "f(x)=%o\n", f;
                        if not f in functions then
                            Append(~functions, f);
                        end if;
                    end if;
                end if;
            end for;
        end for;
    end for;
end procedure;

procedure TangCarletTang(n, ~functions)
    printf "\nTangCarletTang:\n";
    if IsOdd(n) then
        printf "n must be even.\n";
        return;
    end if;

    inv := y^(2^n - 2);

    Valid := [];
    for u in F do
        if u ne 0 and u ne 1 then
            if Trace(1/u) eq 1 and Trace(1/(u+1)) eq 1 then
                Append(~Valid, u);
            end if;
        end if;
    end for;

    Pairs := [];
    Used := {};
    for u in Valid do
        if not (u in Used) then
            Include(~Used, u);
            Include(~Used, u+1);
            Append(~Pairs, {u, u+1});
        end if;
    end for;
    NumPairs := #Pairs;
    // iterate over all subsets of these pairs
    for mask in [0 .. 2^NumPairs - 1] do
        T := {};
        for i in [1..NumPairs] do
            if BitwiseAnd(mask, 2^(i-1)) ne 0 then
                T join:= Pairs[i];
            end if;
        end for;

        f := inv;

        for u in T do
            Iu := 1 - (y + u)^(2^n - 1);
            correction := ((y + 1)^(2^n-2) - inv) * Iu;
            f +:= correction;
        end for;

        if IsPermutation(f, F) then
            du := DiffUniformity(f, F);
            if du eq 4 then
                //printf "f(x) = %o\n", f;
                if not f in functions then
                    Append(~functions, f);
                end if;
            end if;
        end if;
    end for;
end procedure;

procedure ZhaHuSunShan(n, ~functions)
    printf "\nZhaHuSunShan:\n";
    oneQ := Q!1;
    invQ := y^(2^n - 2);
    function IndicatorQ(k)
        Ys := y^(2^k);  // frobenius in Q
        g := (Ys + y)^(2^n - 1);
        return oneQ - g;
    end function;

    evenDivs := [k : k in Divisors(n) | IsEven(k) and k lt n];
    for k1 in evenDivs do
        for k2 in evenDivs do
            if k2 lt k1 then continue; end if;  

            I1 := IndicatorQ(k1);
            I2 := IndicatorQ(k2);
            IS := I1 + I2 - I1*I2;     
            fQ := invQ + IS;  
            f := P!fQ;

            if IsPermutation(f, F) then
                du := DiffUniformity(f, F);
                if du eq 4 then
                    //printf "f(x) = %o\n", f;
                    if not f in functions then
                        Append(~functions, f);
                    end if;
                end if;
            end if;
        end for;
    end for;

    if (n mod 3 eq 0) and IsOdd(n div 6) then
        for k1 in evenDivs do
            if GCD(3, k1) ne 1 then continue; end if;

            I3 := IndicatorQ(3);
            I1 := IndicatorQ(k1);
            IS := I3 + I1 - I3*I1;
            fQ := invQ + IS;
            f := P!fQ;

            if IsPermutation(f, F) then
                du := DiffUniformity(f, F);
                if du eq 4 then
                    //printf "f(x) = %o\n", f;
                    if not f in functions then
                        Append(~functions, f);
                    end if;
                end if;
            end if;
        end for;
    end if;
end procedure;

procedure QuTanLiGong(n, ~functions, boolList)
    printf "\nQuTanLiGong:\n";
    invQ := y^(2^n - 2);
    oneQ := Q!1;

    for g in boolList do
        fQ := invQ + Q!g;
        f := P!fQ;
        if IsPermutation(f, F) then
            du := DiffUniformity(f, F);
            if du eq 4 then
                //printf "f(x) = %o\n", f;
                if not f in functions then
                    Append(~functions, f);
                end if;
            end if;
        end if;
    end for;
end procedure;


procedure CalderiniRandom(n, ~functions)
    printf "\nCalderini Random:\n";
    if (n lt 6) or (not IsEven(n)) then
        printf "must be even n >= 6\n"; return;
    end if;

    GF2 := GF(2);
    K<bk> := GF(2, n-1);
    qK := 2^(n-1);

    // fixed ordering of elements of K
    Klist := [K | z : z in K];
    // index lookup
    Kidx := AssociativeArray();
    for i in [1..#Klist] do
        Kidx[Klist[i]] := i;
    end for;

    VF2, toVF2 := VectorSpace(F, GF2);
    fromVF2 := Inverse(toVF2);

    VK2, toVK2 := VectorSpace(K, GF2);
    fromVK2 := Inverse(toVK2);

    function InvK(z)
        if z eq 0 then return K!0; end if;
        return z^(qK - 2);
    end function;

    // split u in F into (xprime in K, xn in GF(2))
    function Split(u)
        bits := Eltseq(toVF2(u));  // length n, entries in GF(2)
        xn := bits[n];
        xvec := VK2!bits[1..n-1];
        xprime := fromVK2(xvec);
        return xprime, xn;
    end function;

    // merge (xprime in K, xn in GF(2)) back into F
    function Merge(xprime, xn)
        bits := Eltseq(toVK2(xprime));     // length n-1
        return fromVF2(VF2!(bits cat [xn]));
    end function;


    function RandomBoolFuncK(Klist, Kidx)
        vals := [GF(2) | Random(GF(2)) : i in [1..#Klist]];
        return func<z | vals[Kidx[K!z]]>;
    end function;

    M := 200;
    BoolFuncsK := [RandomBoolFuncK(Klist, Kidx) : t in [1..M]];

    // // arbitrary boolean function: all linear boolean functions on K
    // BoolFuncsK := [func<z | Trace(t*z)> : t in K];
    
    for c in K do
        if c eq 0 or c eq 1 then continue; end if;
        if Trace(c) ne GF2!1 then continue; end if;
        if Trace(InvK(c)) ne GF2!1 then continue; end if;

        for bf in BoolFuncsK do
            function MapF(u)
                xprime, xn := Split(u);
                if xn eq GF2!0 then
                    yprime := InvK(xprime); // 1/x'
                    ybit   := bf(xprime);   // f(x')
                else
                    yprime := c * InvK(xprime);     // c/x'
                    ybit   := bf(xprime/c) + GF2!1; // f(x'/c)+1
                end if;
                return Merge(yprime, ybit);
            end function;

            f := PolyFromMap(F, P, MapF);

            if IsPermutation(f, F) then
                du := DiffUniformity(f, F);
                if du eq 4 then
                    //printf "f=%o\n", f;
                    if not (f in functions) then
                        Append(~functions, f);
                    end if;
                end if;
            end if;
        end for;
    end for;
end procedure;



procedure Calderini(n, ~functions)
    printf "\nCalderini:\n";
    if (n lt 6) or (not IsEven(n)) then
        printf "must be even n >= 6\n"; return;
    end if;

    GF2 := GF(2);
    K<bk> := GF(2, n-1);
    qK := 2^(n-1);

    VF2, toVF2 := VectorSpace(F, GF2);
    fromVF2 := Inverse(toVF2);

    VK2, toVK2 := VectorSpace(K, GF2);
    fromVK2 := Inverse(toVK2);

    function InvK(z)
        if z eq 0 then return K!0; end if;
        return z^(qK - 2);
    end function;

    // split u in F into (xprime in K, xn in GF(2))
    function Split(u)
        bits := Eltseq(toVF2(u));  // length n, entries in GF(2)
        xn := bits[n];
        xvec := VK2!bits[1..n-1];
        xprime := fromVK2(xvec);
        return xprime, xn;
    end function;

    // merge (xprime in K, xn in GF(2)) back into F
    function Merge(xprime, xn)
        bits := Eltseq(toVK2(xprime));  // length n-1
        return fromVF2(VF2!(bits cat [xn]));
    end function;

    function PaperBoolF(z)
        if z eq 1 then return GF(2)!0; end if;
        return Trace(1/(z+1));
    end function;

    bf := func< z | PaperBoolF(z)>;
    
    for c in K do
        if c eq 0 or c eq 1 then continue; end if;
        if Trace(c) ne GF2!1 then continue; end if;
        if Trace(InvK(c)) ne GF2!1 then continue; end if;

        function MapF(u)
            xprime, xn := Split(u);
            if xn eq GF2!0 then
                yprime := InvK(xprime); // 1/x'
                ybit   := bf(xprime);   // f(x')
            else
                yprime := c * InvK(xprime);     // c/x'
                ybit   := bf(xprime/c) + GF2!1; // f(x'/c)+1
            end if;
            return Merge(yprime, ybit);
        end function;

        f := PolyFromMap(F, P, MapF);

        if IsPermutation(f, F) then
            du := DiffUniformity(f, F);
            if du eq 4 then
                //printf "f=%o\n", f;
                if not (f in functions) then
                    Append(~functions, f);
                end if;
            end if;
        end if;
    end for;
end procedure;


procedure ChenDengZhuQu(n, ~functions, boolList)
    printf "\nChenDengZhuQu:\n";
    if IsOdd(n) then
        printf "n must be even.\n"; return;
    end if;
    invQ := y^(2^n - 2);
    invP := P!invQ;

    for bP in boolList do
        bInvP := Evaluate(bP, invP);
        fQ := invQ + Q!bInvP;
        f  := P!fQ;

        if IsPermutation(f, F) then
            du := DiffUniformity(f, F);
            if du eq 4 then
                //printf "f(x) = %o\n", f;
                if not f in functions then
                    Append(~functions, f);
                end if;
            end if;
        end if;
    end for;
end procedure;



procedure QuTanTanLi(n, ~functions)
    printf "\nQuTanTanLi:\n";
    if not IsEven(n) then
        printf "n must be even\n"; return;
    end if;
    if not IsOdd(n div 2) then
        printf "n div 2 must be odd\n"; return;
    end if;

    invQ := y^(2^n - 2);

    // Case (1): U = {0,1}
    U1 := { F!0, F!1 };
    IU1 := IndicatorSetQ(U1, n, Q, y);
    fQ  := invQ + IU1;
    f   := P!fQ;
    if IsPermutation(f, F) then
        du := DiffUniformity(f, F);
        //printf "f(x) = %o\n", f;
        if du eq 4 and not (f in functions) then
            Append(~functions, f);
        end if;
    end if;

    // Cases (2) and (3): iterate alpha
    for alpha in F do
        if alpha eq 0 or alpha eq 1 then
            continue;
        end if;

        // ensure {alpha, alpha^2} has size 2
        if alpha^2 eq alpha then
            continue;
        end if;

        U2 := { alpha, alpha^2 };
        IU2 := IndicatorSetQ(U2, n, Q, y);
        fQ  := invQ + IU2;
        f   := P!fQ;
        if IsPermutation(f, F) then
            du := DiffUniformity(f, F);
            //printf "f(x) = %o\n", f;
            if du eq 4 and not (f in functions) then
                Append(~functions, f);
            end if;
        end if;

        U3 := { F!0, F!1, alpha, alpha^2 };
        IU3 := IndicatorSetQ(U3, n, Q, y);
        fQ  := invQ + IU3;
        f   := P!fQ;
        if IsPermutation(f, F) then
            du := DiffUniformity(f, F);
            //printf "f(x) = %o\n", f;
            if du eq 4 and not (f in functions) then
                Append(~functions, f);
            end if;
        end if;
    end for;
end procedure;

procedure Butterfly1(n, ~functions)
    printf "\nButterfly (case 1):\n";
    if not IsEven(n) then
        printf "n must be even\n"; return;
    end if;
    k := n div 2;
    if not IsOdd(k) then
        printf "k must be odd\n"; return;
    end if;

    K := SubfieldK(F, a, n, k);
    VF, toVF := VectorSpace(F, K);
    fromVF := Inverse(toVF);

    function Split(u)
        v := toVF(u);
        s := Eltseq(v);
        return K!s[1], K!s[2];
    end function;

    function Merge(x1, x2)
        return fromVF(VF![K!x1, K!x2]);
    end function;

    function Rxy(x1, y1, alpha, i)
        return (x1 + alpha*y1)^(2^i + 1) + y1^(2^i + 1);
    end function;

    for i in [1..k-1] do
        if Gcd(i, k) ne 1 then continue; end if;

        for alpha in K do
            if alpha eq 0 then continue; end if;

            // build inverse tables for Ry(x)=R(x,y)
            invRy := AssociativeArray();
            good := true;

            for y1 in K do
                tab := AssociativeArray();
                for x1 in K do
                    tab[Rxy(x1, y1, alpha, i)] := x1;
                end for;

                if #Keys(tab) ne #K then
                    good := false; break;
                end if;

                invRy[y1] := tab;
            end for;

            if not good then continue; end if;

            function MapF(u)
                x, y1 := Split(u);
                xhat := invRy[y1][x];
                out1 := Rxy(y1, xhat, alpha, i);
                out2 := xhat;
                return Merge(out1, out2);
            end function;

            poly := PolyFromMap(F, P, MapF);

            if IsPermutation(poly, F) then
                du := DiffUniformity(poly, F);
                if du eq 4 then
                    //printf "f(x) = %o\n", poly;
                    if not (poly in functions) then
                        Append(~functions, poly);
                    end if;
                end if;
            end if;
        end for;
    end for;
end procedure;


procedure Butterfly2(n, ~functions)
    printf "\nButterfly (case 2):\n";
    if not IsEven(n) then
        printf "n must be even\n"; return;
    end if;
    k := n div 2;
    if not IsOdd(k) then
        printf "k must be odd\n"; return;
    end if;

    K := SubfieldK(F, a, n, k);
    VF, toVF := VectorSpace(F, K);
    fromVF := Inverse(toVF);

    function Split(u)
        v := toVF(u);
        s := Eltseq(v);
        return K!s[1], K!s[2];
    end function;

    function Merge(x1, x2)
        return fromVF(VF![K!x1, K!x2]);
    end function;

    function Rxy(x1, y1, alpha, beta)
        return (x1 + alpha*y1)^3 + beta*y1^3;
    end function;

    for alpha in K do
        if alpha eq 0 then continue; end if;

        for beta in K do
            if beta eq 0 then continue; end if;
            if beta eq (1 + alpha)^3 then continue; end if;

            invRy := AssociativeArray();
            good := true;

            for y1 in K do
                tab := AssociativeArray();
                for x1 in K do
                    tab[Rxy(x1, y1, alpha, beta)] := x1;
                end for;

                if #Keys(tab) ne #K then
                    good := false; break;
                end if;

                invRy[y1] := tab;
            end for;

            if not good then continue; end if;

            function MapF(u)
                x, y1 := Split(u);
                xhat := invRy[y1][x];
                out1 := Rxy(y1, xhat, alpha, beta);
                out2 := xhat;
                return Merge(out1, out2);
            end function;

            poly := PolyFromMap(F, P, MapF);

            if IsPermutation(poly, F) then
                du := DiffUniformity(poly, F);
                if du eq 4 then
                    //printf "f(x) = %o\n", poly;
                    if not (poly in functions) then
                        Append(~functions, poly);
                    end if;
                end if;
            end if;
        end for;
    end for;
end procedure;

procedure PengTan1(n, ~functions, Tlist)
    printf "\nPengTan1:\n";
    invQ := y^(2^n - 2);

    for T in Tlist do
        IT := IndicatorSetQ(T, n, Q, y);     // 0/1 in Q
        fQ := invQ + IT;
        f  := P!fQ;
        if IsPermutation(f, F) then
            du := DiffUniformity(f, F);
            if du eq 4 then
                //printf "f=%o\n", f;
                if not (f in functions) then
                    Append(~functions, f);
                end if;
            end if;
        end if;
    end for;
end procedure;

procedure PengTan2(n, ~functions)
    printf "\nPengTan2:\n";
    for s in Divisors(n) do
        if s eq n then continue; end if;
        Fs := sub< F | a^((2^n - 1) div (2^s - 1)) >;

        // t(y) = (y^{2^s} + y)^{2^n-1} is 0 on Fs, 1 off Fs
        tQ := (y^(2^s) + y)^(2^n - 1);

        // I_s(y) = 1 + tQ is 1 on Fs, 0 off Fs
        IsQ := (Q!1) + tQ;

        denomQ := y + (Q!1) + tQ;

        // inverse in F_{2^n} as exponent 2^n-2 (0 maps to 0)
        invDenomQ := denomQ^(2^n - 2);

        // iterate alpha in Fs and beta in Fs*
        for alpha0 in Fs do
            alpha := F!alpha0;
            for beta0 in Fs do
                if beta0 eq 0 then continue; end if;
                beta := F!beta0;
                fQ := (Q!beta) * invDenomQ + (Q!alpha) * IsQ;
                f := P!fQ;

                if IsPermutation(f, F) then
                    du := DiffUniformity(f, F);
                    if du eq 4 then
                        //printf "f=%o\n", f;
                        if not (f in functions) then
                            Append(~functions, f);
                        end if;
                    end if;
                end if;
            end for;
        end for;
    end for;
end procedure;

procedure PengTanWang(n, ~functions)
    printf "\nPengTanWang:\n";
    if (n lt 6) or (not IsEven(n)) then
        printf "must be even n >= 6\n"; return;
    end if;

    invQ := y^(2^n - 2);

    for gamma in F do
        if gamma eq 0 or gamma eq 1 then continue; end if;

        d := Order(gamma);
        if d le 1 then
            continue;
        end if;

        H := { gamma^k : k in [0..d-1] }; 

        // collect coset reps (one per coset) in a simple way
        reps := [];
        used := {};
        for g in F do
            if g eq 0 then continue; end if;
            if g in used then continue; end if;

            Append(~reps, g);
            used join:= { g*h : h in H };
        end for;

        // build U for s=1..#reps by taking first s cosets
        U := {};
        for s in [1..#reps] do
            U join:= { reps[s]*h : h in H };
            IU := IndicatorSetQ(U, n, Q, y);
            invGamY := (Q!gamma * y)^(2^n - 2);
            fQ := invQ + IU * (invGamY - invQ);
            f  := P!fQ;

            if IsPermutation(f, F) then
                du := DiffUniformity(f, F);
                if du eq 4 then
                    //printf "f=%o\n", f;
                    if not (f in functions) then
                        Append(~functions, f);
                    end if;
                end if;
            end if;
        end for;
    end for;
end procedure;

procedure XuQu(n, ~functions)
    printf "\nXuQu:\n";
    for s in Divisors(n) do
        if s eq n then continue; end if;
        if not IsEven(s) then continue; end if;
        if not IsOdd(n div s) then continue; end if;

        Fs := sub< F | a^((2^n - 1) div (2^s - 1)) >;

        // indicator of Fs
        tQ  := (y^(2^s) + y)^(2^n - 1);   // 0 on Fs, 1 off Fs
        IsQ := (Q!1) + tQ;               // 1 on Fs, 0 off Fs

        invQ := y^(2^n - 2);

        for gamma0 in Fs do
            if gamma0 eq 0 then continue; end if;   // gamma in Fs*
            gamma := F!gamma0;
            invGamY := (Q!gamma * y)^(2^n - 2);
            fQ := invQ + IsQ * (invGamY - invQ);
            f  := P!fQ;

            if IsPermutation(f, F) then
                du := DiffUniformity(f, F);
                if du eq 4 then
                    //printf "f=%o\n", f;
                    if not (f in functions) then
                        Append(~functions, f);
                    end if;
                end if;
            end if;
        end for;
    end for;
end procedure;


// -------------------------


Gold(n, ~functions);
Kasami(n, ~functions);
InverseFam(n, ~functions);
BrackenLeander(n, ~functions);
BrackenTanTan(n, ~functions);
TanQuTanLi1(n, ~functions);
TanQuTanLi2(n, ~functions);
YuWangLi(n, ~functions);
ZhaHuSun1(n, ~functions);
XuCaoXu(n, ~functions);
ZhaHuSun2(n, ~functions);
LiWang1(n, ~functions);
SinKimKimHan(n, ~functions);
TangCarletTang(n, ~functions);
ZhaHuSunShan(n, ~functions);
QuTanLiGong(n, ~functions, boolList);
Calderini(n, ~functions);
//CalderiniRandom(n, ~functions);
ChenDengZhuQu(n, ~functions, boolList);
QuTanTanLi(n, ~functions);
Butterfly1(n, ~functions);
Butterfly2(n, ~functions);
PengTan1(n, ~functions, Tlist);
PengTan2(n, ~functions);
PengTanWang(n, ~functions);
XuQu(n, ~functions);

classes := []; 
unclassified := {1..#functions}; 

while #unclassified gt 0 do 
    i := Minimum(unclassified); 
    base := functions[i]; 
    class := [i]; 
    Exclude(~unclassified, i); 
    for j in unclassified do 
        if CCZeq2(base, functions[j]) then 
            Append(~class, j); 
        end if; 
    end for;
    for idx in class do 
        Exclude(~unclassified, idx); 
    end for; 
    Append(~classes, class); 
end while; 

for c in [1..#classes] do
    idx := classes[c][1]; 
    printf "\nRepresentative of class %o (size %o): %o\n", c, #classes[c], functions[idx];
end for;