# A maple code for the dual Leipniz-Hopf(LH) algebra
# Description: This code includes functions to compute
# the orverlapping product and the conjugation in the dual
# Leipniz-Hopf algebra
# Author: S. Kaji (Yamaguchi University, Japan)
# Version history: initial version -- 2 Feb. 2014.
#                  current version -- 2 Jan. 2015.
# Global variables:
# T[]: basis for LH-algebra
# S[]: basis for dual LH-algebra
# P[]: Cartan-Serre basis for Steenrod algebra
# Q[]: Cartan-Serre basis for dual Steenrod algebra
# x[]: Milnor basis for dual Steenrod algebra

with(LinearAlgebra[Modular]);

## the dual Leibniz-Hopf algebra
# overlapping shuffle product
os := proc (f::polynom) local ff, L, t; global p;
    ff := expand(f) mod p;
    if degree(ff) < 2 then
        return ff
    elif op(0, ff) = `+` then
        return expand(map(os, ff)) mod p
    elif op(0, ff) = `*` then
        if type(op(1, ff), 'numeric') then
            return op(1, ff)*os(ff/op(1, ff)) mod p;
        elif nops(ff) = 2 and type(op(1, ff), 'indexed') and type(op(2, ff), 'indexed') then
            L := osw(op(1, op(1, ff)), op(1, op(2, ff)));
            return `mod`(add(S[l], l in L), p)
        else
            return `mod`(expand(os(os(op(1, ff))*os(mul(op(i, ff), i = 2 .. nops(ff))))), p)
        end if;
    elif op(0, ff) = `^` and type(op(1, ff), 'indexed') then
        t := floor(log[p](op(2, ff)));
        if 0 < t then
            return `mod`(os(S[p^t*op(1, op(1, ff))]*op(1, ff)^(op(2, ff)-p^t)), p)
        else L := osw(op(1, op(1, ff)), op(1, op(1, ff)));
            return os(add(S[l], l in L)*op(1, ff)^(op(2, ff)-2))
        end if;
    else
        print(ff, op(0, ff), "Error: no rule to compute the product")
    end if;
end proc;

#overlapping shuffle of two words
osw := proc (v::list, w::list) local L, i; option remember;
    if nops(w) = 0 then
        return [v]
    end if;
    if nops(v) = 0 then
        return [w]
    end if;
    L := [seq([w[1], op(x)], x in osw(v, w[2 .. -1]))];
    for i to nops(v) do
        L := [op(L), seq([op(v[1 .. i]), w[1], op(x)], x in osw(v[i+1 .. -1], w[2 .. -1]))];
        L := [op(L), seq([op(v[1 .. i-1]), v[i]+w[1], op(x)], x in osw(v[i+1 .. -1], w[2 .. -1]))]
    end do;
    return L;
end proc;

# pi image of milnor's dual basis
xi := proc (n) local i, x; global p;
    if type(n, 'integer') then
        if n = 0 then
            return 1
        else
            return S[[seq(p^(n-i), i = 1 .. n)]]
        end if
    elif type(n, 'list') then
        x := 1;
        for i to nops(n) do
            x := x*xi(i)^n[i]
        end do;
        return x
    else print("Error: xi")
    end if
end proc;

# convert a polynomial in x to one in S
x2xi := proc(f::polynom) local s,ind;
    ind := [];
    for s in indets(f) do
        if op(0,s)=`x` and type(s,'indexed') then
            ind := [op(ind),op(1,s)]
        end if;
    end do;
    return eval(f,[seq(x[i]=xi(i),i=ind)]);
end proc:

# conjugation for dual LH-algebra
chi := proc (f::polynom) global p;
    if degree(f) < 1 then
        return f
    elif type(f, 'indexed') then
        return add((-1)^nops(op(1, f))*S[x], x in coarsening(ListTools[Reverse](op(1, f))))
    elif op(0, f) = `+` then
        return `mod`(map(chi, f), p)
    elif op(0, f) = `*` then
        if type(op(1, f), 'numeric') then
            return `mod`(op(1, f)*chi(f/op(1, f)), p)
        else
            return `mod`(chi(op(1, f))*chi(mul(op(i, f), i = 2 .. nops(f))), p)
        end if
    elif op(0, f) = `^` then
        return `mod`(chi(op(1, f))^op(2, f), p)
    else
        print("cannot compute chi:", f, op(0, f))
    end if
end proc;

# conjugation for LH-algebra
chi2 := proc (f::polynom) global p;
    if degree(f) < 1 then
        return f
    elif type(f, 'indexed') then
        return add((-1)^nops(op(1, f))*T[x], x in refinement(ListTools[Reverse](op(1, f))))
    elif op(0, f) = `+` then
        return `mod`(map(chi2, f), p)
    elif op(0, f) = `*` then
        if type(op(1, f), 'numeric') then
            return `mod`(op(1, f)*chi2(f/op(1, f)), p)
        else
            return `mod`(chi2(op(1, f))*chi2(mul(op(i, f), i = 2 .. nops(f))), p)
        end if
    elif op(0, f) = `^` then
        return `mod`(chi2(op(1, f))^op(2, f), p)
    else
        print("cannot compute chi2:", f, op(0, f))
    end if
end proc;

# retraction onto the dual steenrod algebra (taking admissble terms)
retract := proc (f::polynom) local ff, i, w; global p;
    ff := expand(f);
    if 1 < degree(ff) then
        print(ff, "input must be linear")
    elif op(0, ff) = `+` then
        return map(retract, ff)
    elif type(ff, 'indexed') then
        if op(0,ff) != `S` then return ff; end if;
        w := op(1, ff);
        for i to nops(w)-1 do
            if w[i] < p*w[i+1] then
                return 0
            end if
        end do;
        return Q[w]
    elif op(0, ff) = `*` and type(op(1, ff), 'numeric') then
        return `mod`(op(1, ff)*retract(ff/op(1, ff)), p)
    else
        print("cannot compute retract:",ff, op(0, ff));
        return 0
    end if
end proc;

# projection onto the steenrod algebra (applying Adem relations)
projection := proc (f::polynom) local ff, i, w, t, j; global p;
    ff := expand(f) mod p;
    if 1 < degree(ff) then
        print(ff, "input must be linear")
    elif type(ff,'numeric') then
        return ff;
    elif op(0, ff) = `+` then
        return map(procname, ff) mod p
    elif type(ff, 'indexed') then
        if op(0,ff) != `T` and op(0,ff) != `P` then return ff; end if;
        w := op(1, ff);
        for i to nops(w)-1 do
            if w[i] < p*w[i+1] then
                t := ((-1)^(w[i]))*binomial((p-1)*w[i+1]-1,w[i])
                      *P[[op(w[1..i-1]),w[i]+w[i+1],op(w[i+2..-1])]];
                for j to floor(w[i]/p) do
                    t:=t + ((-1)^(w[i]+j))*binomial((p-1)*(w[i+1]-j)-1,w[i]-p*j)
                      *P[[op(w[1..i-1]),w[i]+w[i+1]-j,j,op(w[i+2..-1])]];
                end do;
                return procname(t mod p);
            end if
        end do;
        return P[w]
    elif op(0, ff) = `*` and type(op(1, ff), 'numeric') then
        return `mod`(op(1, ff)*procname(ff/op(1, ff)), p)
    else
        print("cannot compute projection:",ff, op(0, ff));
        return 0
    end if
end proc;

## Combinatorics on words
# ordered partition of an integer
ordpart := proc (n::integer) local L, V; option remember;
    if n = 0 then
        return []
    elif n = 1 then
        return [[1]]
    end if;
    L := ordpart(n-1);
    V[1] := [seq([1, op(v)], v in L)];
    V[2] := [seq([v[1]+1, op(v[2 .. -1])], v in L)];
    return [op(V[1]), op(V[2])]
end proc;
# ordered partition of a list
ordpartlist := proc (L::list) local V, u, i, w, pos;
    V := [];
    for u in ordpart(nops(L)) do
        w := [];
        pos := 1;
        for i in u do
            w := [op(w), L[pos .. pos+i-1]];
            pos := pos+i
        end do;
        V := [op(V), w]
    end do;
    return V
end proc;

# coarsening of a word
coarsening := proc (w::list) local L, p, i, l, v; option remember;
    L := [];
    for p in ordpart(nops(w)) do
        v := [];
        l := 1;
        for i to nops(p) do
            v := [op(v), add(w[j], j = l .. l+p[i]-1)];
            l := l+p[i]
        end do;
        L := [op(L), v]
    end do;
    return L
end proc;

# refinement of a word
refinement := proc (w::list) local L, l, v, U; option remember;
    if nops(w)=1 then
        return ordpart(w[1]);
    else
        U := [];
        L := refinement(w[2..-1]);
        for v in ordpart(w[1]) do
            for l in L do
                U := [op(U), [op(v),op(l)]];
            end do;
        end do;
        return U;
    end if;
end proc:

# list monomials of degree "totaldeg" consisting of "gens",
# whose degrees are specified by "degs"
list_monom := proc (gens::list, degs::(list(integer)), totaldeg::integer) local v, L, V;
    L := wpartition(degs, totaldeg);
    V := [];
    for v in L do
        V := [op(V), mul(gens[i]^v[i], i = 1 .. nops(v))]
    end do;
    return V
end proc;

# weighted partition; express "totaldeg" as linear combinations of "degs"
wpartition := proc (degs::(list(integer)), totaldeg::integer) local i, L, V;
    L := [];
    if totaldeg = 0 then
        return [[seq(0, i = 1 .. nops(degs))]]
    elif nops(degs) = 0 then
        return []
    elif nops(degs) = 1 then
        if `mod`(totaldeg, degs[1]) = 0 then
            return [[totaldeg/degs[1]]]
        else
            return []
        end if
    end if;
    for i from floor(totaldeg/degs[-1]) by -1 to 0 do
        V := wpartition(degs[1 .. -2], totaldeg-i*degs[-1]);
        L := [op(L), seq([op(v), i], v in V)]
    end do;
    return L
end proc;

## Enumerating basis and the conjugation invariants
# enumerate admissible sequences with lex order
admseq := proc (totaldeg::integer) local n, L; global p;
    n := floor(log[p]((p-1)*totaldeg+1));
    L := wpartition([seq((p^i-1)/(p-1), i = 1 .. n)], totaldeg);
    return map(ex2adm, L)
end proc;

# convert excess representation to admissible sequence
ex2adm := proc (ex::list) local n; global p;
    n := nops(ex);
    while ex[n] = 0 do
        n := n-1
    end do;
    return [seq(add(p^(i-j)*ex[i], i = j .. nops(ex)), j = 1 .. n)]
end proc;

# enumerate pi image of milnor monomials of degree "deg"
milnor_images := proc (deg::integer) local L, V, i, s, n; global p;
    V := [];
    n := floor(log[p]((p-1)*deg+1));
    L := list_monom([seq(x[i], i = 1 .. n)], [seq((p^i-1)/(p-1), i = 1 .. n)], deg);
    for s in L do
        V := [op(V), s = os(eval(s, [seq(x[i] = xi(i), i = 1 .. n)]))]
    end do;
    return V
end proc;

# polynomial associated to a list
pp := proc (L::list) local x, w;
    x := 0;
    for w in L do
        x := x+mul(S[u], u in w)
    end do;
    return x
end proc;

# linear equation solver
# Solves equations L in terms of indeterminants A
sol := proc (L::list, A::list) local X, V, i, j, v, n, Y,Z, rp, d, R, U, r; global p;
    n := nops(L);
    X := Matrix(n, n+nops(A));
    for i to n do
        X[i, nops(A)+i] := 1;
        for j to nops(A) do
            X[i, j] := coeff(op(2, L[i]), A[j])
        end do
    end do;
    X := Mod(p, X, integer[]);
    U := Mod(p, X, integer[]);
    Y, rp, d := RowEchelonTransform(p, U, true, true, false, false);
    r := nops(rp); U := U[1 .. n, 1 .. n];
    Z := LinearAlgebra[IdentityMatrix](n, compact = false);
    for i to LinearAlgebra[Dimension](Y) do
        LinearAlgebra[RowOperation](Z, [i, Y[i]], inplace = true)
    end do;
    Z := Mod(p, Z, integer[]);
    X := Multiply(p, Z, X);
    X := Multiply(p, U, X);
    V := [];
    for v in convert(X, listlist) do
        V := [op(V), add(v[i]*A[i], i = 1 .. nops(A)) = add(v[nops(A)+i]*op(1, L[i]), i = 1 .. nops(L))]
    end do;
    return V
end proc;

# compute conjugation invariants in degree "deg" in the dual Steenrod algebra
conjinvQ := proc (deg::integer) local L, V, U, v, w; global p;
    L := milnor_images(deg);
    V := [];
    for v in L do
        V := [op(V), op(1, v) = `mod`(chi(op(2, v))-op(2, v), p)]
    end do;
    U := [];
    for v in sol(V, [seq(S[w], w=admseq(deg))]) do
        if op(1,v)=0 then
            U:=[op(U), [op(2, v),retract(os(x2xi(op(2,v))))]];
        end if;
    end do:
    return U;
end proc;
# compute conjugation invariants in degree "deg" in the dual LH algebra
conjinvS := proc (deg::integer) local L, V, U, v, w; global p;
    L := ordpart(deg);
    V := [];
    for v in L do
        V := [op(V), S[v] = `mod`(chi(S[v])-S[v], p)]
    end do;
    U:=[];
    for v in sol(V, [seq(S[w], w=L)]) do
        if op(1, v) = 0 then
            U:=[op(U),srt(op(2, v))]
        end if;
    end do;
    return U
end proc;
# compute conjugation invariants in degree "deg" in the LH algebra
conjinvT := proc (deg::integer) local L, V, U, v, w; global p;
    L := ordpart(deg);
    V := [];
    for v in L do
        V := [op(V), T[v] = `mod`(chi2(T[v])-T[v], p)]
    end do;
    U:=[];
    for v in sol(V, [seq(T[w], w=L)]) do
        if op(1, v) = 0 then
            U:=[op(U),srt(op(2, v))]
        end if;
    end do;
    return U
end proc;
# compute conjugation invariants in degree "deg" in the Steenrod algebra
conjinvP := proc (deg::integer) local L, V, U, v; global p;
    L := admseq(deg);
    V := [];
    for v in L do
        V := [op(V), P[v] = projection(chi2(T[v]) - T[v]) mod p]
    end do;
    U:=[];
    for v in sol(V, [seq(P[w],w=L)]) do
        if op(1, v) = 0 then
            U:=[op(U),srt(op(2, v))]
        end if;
    end do;
    return U
end proc;

# sort terms in reverse lex order
srt := proc (f::polynom) local L;
    if degree(f) <> 1 then
        print("degree must be one", f);
        return f
    end if;
    L := sort([seq(ListTools[Reverse](op(1, s)), s in indets(f))]);
    L := [seq(S[ListTools[Reverse](l)], l in L)];
    return
    sort(f, L)
end proc;

# duality between S_I and T^J
# Note that S_J is conjugation invariant <=> So is T^K in non-dual LH-algebra
dual := proc (f::{polynom,list}) local J,K,k,Sym;
    if op(0, f) = `+` or type(f,'list') then
        return map(dual, f);
    elif op(0, f) = `*` then
        if type(op(1, f), 'numeric') then
            return op(1, f)*dual(f/op(1, f));
        else
            print("cannot compute dual :",f);
        end if;
    elif type(f, 'indexed') then
        if op(0,f)=`S` then
            Sym := T;
        else
            Sym := S;
        end if;
        k := 0;
        J := op(1,f);
        K := [];
        while nops(J)>0 do
            k := k+1;
            if J[1]=1 then
                J := J[2..-1];
                if nops(J)=0 then
                    K := [op(K),k];
                end if;
            else
                J[1] := J[1]-1;
                K := [op(K),k];
                k := 0;
            end if;
        end do;
        return Sym[K];
    else
            print("cannot compute dual:",f);
    end if;
end proc:
