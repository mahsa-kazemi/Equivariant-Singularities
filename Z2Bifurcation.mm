
with(Student[LinearAlgebra]): 
with(Groebner): 
with(PolynomialIdeals):
#with(LinearAlgebra):
#<-----------------------------------------------------------------------------
# Function: { Z2LT(f_in, vars_in) }
# Briefly: { returns leading term of a germ w.r.t alex ordering }
# Calling sequence:
# { Z2LT(f_in, vars_in) }
# Input:
# { f_in : germ }
# { vars_in : list of variables}
# Output:
# { leading term of a germ w.r.t alex ordering}
#>-----------------------------------------------------------------------------
Z2LT := proc(f,Vars)
local g, A, BC, d, flag, N, i:

  #option trace;
   g:= expand(f);
   if type(g,`+`) then
        A:= [op(g)];
        A:=sort(A,(a,b)-> degree(a) < degree(b));
        d := degree(A[1]);
        flag := false;
        N := NULL;
        for i from 1 to nops(A) while flag=false do 
            if degree(A[i])=d then
               N := N, A[i];
            else
                flag := true;
            fi;
        od;
        BC := [N];
        BC:=sort(BC,(a,b)-> TestOrder(b, a, plex(op(Vars))));
        RETURN(BC[1]);
   else
        RETURN(g);
   fi;
end proc:
#<-----------------------------------------------------------------------------
# Function: { Z2LM(f_in, vars_in) }
# Briefly: { returns leading monomial of a germ w.r.t alex ordering }
# Calling sequence:
# { Z2LM(f_in, vars_in) }
# Input:
# { f_in : germ }
# { vars_in : list of variables}
# Output:
# { leading monomial of a germ w.r.t alex ordering}
#>-----------------------------------------------------------------------------
Z2LM := proc(f,Vars)

   return(LeadingMonomial(Z2LT(f, Vars), plex(op(Vars))));
end proc:
#<-----------------------------------------------------------------------------
# Function: { Z2Spoly(f_in, g_in, vars_in) }
# Briefly: { computes spolynomial of two germs f_in and g_in }
# Calling sequence:
# { Z2Spoly(f_in, g_in, vars_in) }
# Input:
# { f_in : germ }
# { g_in : germ }
# { vars_in : list of variables}
# Output:
# { spolynomials of two input germs}
#>-----------------------------------------------------------------------------
Z2Spoly := proc(f,g,Vars)
local a:
  
  a := lcm(Z2LM(f, Vars), Z2LM(g, Vars));
  return(simplify((a*f)/(Z2LT(f, Vars))-(a*g)/(Z2LT(g, Vars))));
end proc:
#<-----------------------------------------------------------------------------
# Function: { Z2MoraNFM(f_in, F_in, vars_in) }
# Briefly: { returns remainder of the division of f_in by F_in using Mora Method }
# Calling sequence:
# { Z2MoraNFM(f_in, F_in, vars_in) }
# Input:
# { f_in : germ }
# { F_in : list of germs}
# { vars_in : list of variables}
# Output:
# { Mora remainder}
#>-----------------------------------------------------------------------------
Z2MoraNFM := proc(f,F,Vars)
local h, L, M, t, A, g,l:

  h := f;
  L := F;
  l:=x->divide(Z2LT(h,Vars),Z2LT(x,Vars));
  M:=select(l,L);
  while h<>0 and nops(M)<>0 do
      #A:=sort([seq([ecart(i, Vars), i], i = M)],(a,b)-> a[1]< b[1]);
       A:=sort(M,(a,b)->Z2NEWTEST(a,b,Vars));
       g := A[1];
       if Z2ecart(g,Vars)>Z2ecart(h,Vars) then
           L := [op(L),h];
       fi;
       h := simplify(h-Z2LT(h, Vars)*g/Z2LT(g, Vars));
          if h<>0 then
             l:=x->divide(Z2LT(h,Vars),Z2LT(x,Vars));
             M:=select(l,L);
          fi;
  od;
  RETURN(h);
end proc:
#<-----------------------------------------------------------------------------
# Function: { Z2FindPower(v_in, F_in, vars_in) }
# Briefly: { }
# Calling sequence:
# { Z2FindPower(v_in, F_in, vars_in) }
# Input:
# { v_in : }
# { F_in : }
# { vars_in :}
# Output:
# { }
#>-----------------------------------------------------------------------------
Z2FindPower := proc(F, vars)
local flag, i, F1, NEWPOINT, w, M, p :

  F1:=Z2STD(F,vars); 
  NEWPOINT:=NULL; 
  for w in vars do         
       M:=Z2MultMatrix(F1,w, vars):         
       p:=MinimalPolynomial(M,w):
       NEWPOINT:=NEWPOINT,degree(p);
  od:  
  return [NEWPOINT, F1]:  
end proc:
#<-----------------------------------------------------------------------------
# Function: {Z2Intrinsic (I_in, vars_in) }
# Briefly: { }
# Calling sequence:
# { Z2Intrinsic (I_in) }
# Input:
# { I_in : }
# { vars_in : }
# Output:
# { }
#>-----------------------------------------------------------------------------
ready_Intrinsic := proc(L_in, vars_in)
local L, vars, L_out, h_in:
	L := [seq(simplify((g_in)/vars_in[1]), g_in=L_in)];
	vars := [u, vars_in[2]];
	L := algsubs(vars_in[1]^2=u, L);
	L_out := Z2Intrinsic(L, vars);
	L_out := algsubs(u=vars_in[1]^2, L_out);
	L_out := [seq(expand(vars_in[1]*h_in), h_in=L_out)];
	return(L_out);
end proc:

Intrinsic := proc()
	if evalb(nargs=3 and lhs(args[3])='symmetry' and rhs(args[3])='Z2') then
		return(ready_Intrinsic(args[1], args[2]));
	end if:
end proc:

Z2Intrinsic := proc(I_in, vars_in)
local  u_new, lambda_new, A, i, j, t, z, flag, k, I_out:
 #option trace:

  u_new := Z2FindPower(I_in, vars_in)[1]:
  lambda_new := Z2FindPower(I_in, vars_in)[2];
  I_out := Z2FindPower (I_in, vars_in)[3]:
  A := NULL;
  i := u_new-1:
  j := lambda_new-1:
  for z from 1 to i do
     flag := false;
     for k from 1 to j  while flag = false do
         if Z2MoraNFM(vars_in[1]^z*vars_in[2]^k, I_out, vars_in) = 0 and nops([A])=0 then
             flag := true;
             A := A, vars_in[1]^z*vars_in[2]^k;
         elif Z2MoraNFM(vars_in[1]^z*vars_in[2]^k, I_out, vars_in) = 0 and nops([A])<>0 then
             if z>= degree([A][-1], vars_in[1]) and k>= degree([A][-1], vars_in[2]) then
                  flag := true;
                  A :=A;
              else
                  flag := true;
                  A := A, vars_in[1]^z*vars_in[2]^k;
              end if:
        end if:
     end do:
 end do:
 return([vars_in[1]^u_new, A, vars_in[2]^lambda_new]):
end proc:
#<-----------------------------------------------------------------------------
# Function: { Z2NEWTEST(z_in, w_in, vars_in) }
# Briefly: { }
# Calling sequence:
# { Z2NEWTEST(z_in, w_in, vars_in) }
# Input:
# { z_in : }
# { w_in : }
# { vars_in : }
# Output:
# { }
#>-----------------------------------------------------------------------------
Z2NEWTEST := proc(Z,W,Vars)

  if Z2ecart(Z,Vars)<Z2ecart(W,Vars) then
     return(true);
  elif Z2ecart(Z,Vars)>Z2ecart(W,Vars) then
     return(false);
  elif Z2ecart(Z,Vars)=Z2ecart(W,Vars) and Z2TEST(Z2LM(Z,Vars),Z2LM(W,Vars),Vars)=true then
     return(true);
  elif Z2ecart(Z,Vars)=Z2ecart(W,Vars) and Z2TEST(Z2LM(Z,Vars),Z2LM(W,Vars),Vars)=false then
     return(false);
  fi;
end proc:
#<-----------------------------------------------------------------------------
# Function: { Z2TEST(a_in, c_in, vars_in) }
# Briefly: { }
# Calling sequence:
# { Z2TEST(a_in, c_in, vars_in) }
# Input:
# { a_in : }
# { c_in : }
# { vars_in : }
# Output:
# { }
#>-----------------------------------------------------------------------------
Z2TEST := proc(A,C,Vars)
   if degree(A)<degree(C) then
      return(false);
   elif degree(A)>degree(C) then
      return(true);
   elif degree(A)=degree(C) and TestOrder(A,C,plex(op(Vars)))=true then
      return(true);
   elif degree(A)=degree(C) and TestOrder(A,C,plex(op(Vars)))=false then
      return(false);
    fi;
end:
#<-----------------------------------------------------------------------------
# Function: {Z2ecart (f_in, vars_in) }
# Briefly: { }
# Calling sequence:
# { Z2ecart (f_in, vars_in) }
# Input:
# { f_in : }
# { vars_in : }
# Output:
# { }
#>-----------------------------------------------------------------------------
Z2ecart := proc(f,Vars)

  return(degree(f)-degree(Z2LT(f, Vars))):
end:
#<-----------------------------------------------------------------------------
# Function: {Z2MultMatrix(S_in, u_in)}
# Briefly: { }
# Calling sequence:
# {Z2MultMatrix(S_in, u_in)}
# Input:
# { }
# Output:
# { }
#>-----------------------------------------------------------------------------
Z2MultMatrix:=proc(S,u, vars)
local L,n,M,i,v,j,c;

   L:=Z2NSet([seq(Z2LM(z, vars), z=S)], vars);
   n:=nops(L);
   M:=Matrix(n);
   for i from 1 to n do
       v:=Z2MoraNFM(u*L[i],S, vars);
       M[1,i]:=simplify(v,indets(L));
       for j from 2 to n do
           c:=coeff(subs(L[j]=Maple,v),Maple);
           if degree(c)=0 then
               M[j,i]:=c;
           fi;
       od;
   od;
   RETURN(M);
end:
#<-----------------------------------------------------------------------------
# Function: {Z2NSet(LL_in, vars_in)}
# Briefly: { }
# Calling sequence:
# {Z2NSet(LL_in, vars_in)}
# Input:
# { }
# Output:
# { }
#>-----------------------------------------------------------------------------
Z2NSet := proc (LL, vars) 
local g,L,V, d, N, v, x, m, i, j, u, flag, l; 
  L := {seq(Z2LM(f,vars),f=LL)};
return(NormalSet(L,plex(op(vars)))[1]);
  #L:={op(LL)};
  N:=NULL;
  for l in L do
     flag:=false;
     for g in L minus {l} while not flag do
        if divide(l,g) then 
            flag:=true;
        fi;
    od;
    if not flag then
         N:=N,l;
    fi;
  od;
  L:=[N];    
  V := indets(L); 
  N := 1; 
  for v in L do 
     if nops(indets(v)) = 1 then 
         x := indets(v)[1]; 
         N := N, seq(x^i, i = 1 .. degree(v)-1); 
    end if; 
  end do; 
  m := nops([N]); 
  for i from 2 to m do 
      for j from i+1 to m do
          if indets(N[i]) <> indets(N[j]) then 
              u := N[i]*N[j]; 
              flag := false; 
              for l in L while not flag do 
                 if divide(u, l) then 
                    flag := true; 
                 end if; 
              end do; 
              if not flag then 
                 N := N, u; 
              end if;
         fi; 
    end do; 
 end do; 
 RETURN([op({N})]); 
end proc:
#<-----------------------------------------------------------------------------
# Function: {}
# Briefly: { }
# Calling sequence:
# {}
# Input:
# { }
# Output:
# { }
#>-----------------------------------------------------------------------------
MakePair:=proc(L)
local A, BB, i, m, W,j;

	A := L;
	BB := NULL;
	for i in A do
		m := A[1];
		A := A[2 .. -1];
		W := [seq([m, j], j in A)];
		BB := BB, op(W);
	od;
	return([BB]);
end proc:
#<-----------------------------------------------------------------------------
# Function: {}
# Briefly: { }
# Calling sequence:
# {}
# Input:
# { }
# Output:
# { }
#>-----------------------------------------------------------------------------
Z2STD:=proc(F::list,vars::list)
local G, P, A, B, h, Q, i, high:
	G := F;
	P := MakePair(F);
	while nops(P)<>0 do 
		A := P[1];
		B := Z2Spoly(A[1], A[2],vars);
		h := Z2MoraNFM(B, G,vars);
		P := P[2 .. -1];
		if h<>0 then 
			Q := NULL;
			for i in G do
				Q := Q, [h, i];
			od;
			P := [op(P), Q];
			G := [op(G), h];
		fi;
	od;
	return(G);
end proc:
#<-----------------------------------------------------------------------------
# Function: {Z2RTVectorPart(L_in, Intrinsic_in, vars_in)}
# Briefly: { computes the vector space part of a submodule }
# Calling sequence:
# {Z2RTVectorPart(L_in, Intrinsic_in)}
# Input:
# { L_in : list of modules elements}
# { Intrinsic_in : intrinsic part of L_in}
# { vars_in : list of variables}
# Output:
# { }
#>-----------------------------------------------------------------------------
Z2RTVectorPart := proc(L_in::list, Intrinsic_in::list, vars_in::list)
 local L, vector_out, elem_in, r;
 
  L := L_in;
  vector_out := NULL;
  for elem_in in L do
     #r := DivAlgFormal(elem_in, Intrinsic_in, 15, vars_in):
	r := Z2MoraNFM(elem_in, Intrinsic_in, vars_i);
     if r<>0 then
        vector_out := vector_out, r;
        L := [vars_in[1]*r, vars_in[2]*r, op(L)];
     end if;
  end do;
  return [vector_out];
end proc:
#<-----------------------------------------------------------------------------
# Function: {Z2TransitionSet}
# Briefly: { }
# Calling sequence:
# {Z2TransitionSet(G_in, vars_in, params_in)}
# Input:
# {G_in : a Z2-equivariant unfolding }
# { }
# { }
# Output:
# { }
#>-----------------------------------------------------------------------------
Z2TransitionSet := proc(G_in, vars, params_in)
local R_befor, R_ready, B1, B1_out, H0, H0_out, H1, H1_out, D_out, D_final, B0, B0_out:
     R_befor := simplify(G_in/vars[1]);
     R_ready := algsubs((vars[1])^2=u, R_befor); 
     B1 := <R_ready, diff(R_ready, u), diff(R_ready,vars[2]), 1-zeta^2*u>;
     B1_out := EliminationIdeal(B1, {op(params_in)});
     B0 := <subs(u=0,R_ready), subs(u=0,diff(R_ready,vars[2]))>;
     if {1} subset IdealInfo:-Generators(B0) then
        B0_out := <1>;
     elif {-1} subset IdealInfo:-Generators(B0) then
	B0_out := <1>;
     else
     B0_out := EliminationIdeal(B0, {op(params_in)});
     end if:
     H0 := <subs(u=0,R_ready), subs(u=0,diff(R_ready,u))>;
     H0_out := EliminationIdeal(H0, {op(params_in)});
     H1 := <R_ready, diff(R_ready, u), diff(R_ready,u$2), 1-zeta^2*u>;
     H1_out := EliminationIdeal(H1, {op(params_in)});
     D_out := <1-zeta*(u[1]-u[2]),u[1]-zeta[1]^2,u[2]-zeta[2]^2,subs(u=u[1],R_ready), subs(u=u[2], R_ready),subs(u=u[1],u*diff(R_ready, u)), subs(u=u[2], u*diff(R_ready,u))>;
     D_final := EliminationIdeal(D_out, {op(params_in)});
     print("B0=", B0_out);
     print("B1=", B1_out);
     print("H0=", H0_out);
     print("H1=", H1_out);
     print("D=", D_final);		
end proc:
#<-----------------------------------------------------------------------------
# Function: {}
# Briefly: { }
# Calling sequence:
# {}
# Input:
# { }
# { }
# { }
# Output:
# { }
#>-----------------------------------------------------------------------------
Z2S := proc(h_in, vars_in::list)
local A, empty_list, i, a_candid, flag, B, b_check, j:
	A := {op(h_in)};
	empty_list := NULL;
	for i from 1 to nops(A) do
		a_candid := A[i];
		flag := true;
		B := A minus {a_candid};
		for b_check in B do
			if divide(a_candid, b_check) then
				flag:= false;
			end if:
		end do:
		if flag then
			empty_list := empty_list,a_candid;
		end if:
	end do:
	return([seq(Z2LM(j, vars_in), j=empty_list)]);#<>
end proc:
#<-----------------------------------------------------------------------------
# Function: {}
# Briefly: { }
# Calling sequence:
# {}
# Input:
# { }
# { }
# { }
# Output:
# { }
#>-----------------------------------------------------------------------------
Z2RT := proc(h_in, vars_in::list)
local L, int_part, vec_part, RT_ready:
	L := [h_in, vars_in[1]*diff(h_in,vars_in[1])];	
	int_part := Z2Intrinsic(L, vars_in);
	vec_part := Z2RTVectorPart(L, int_part, vars_in);
	if nops(vec_part)<>0 then
		RT_ready := int_part+{op(vec_part)};
	else
		RT_ready := int_part;
	end if:
	return(RT_ready);
end proc:
#<-----------------------------------------------------------------------------
# Function: {}
# Briefly: { }
# Calling sequence:
# {}
# Input:
# { }
# { }
# { }
# Output:
# { }
#>-----------------------------------------------------------------------------
Z2P := proc(h_in, vars_in::list)
local rt_in, A,read_out, A_befor, i, j,real_final,read_out_final :
	rt_in := Z2RT(h_in, vars_in);
	if type(rt_in,`+`) then
		A := [op(rt_in)];
		A := [seq(op(i),i=A)];
	else
		A := rt_in;
	end if:
	A_befor := [op({seq(vars_in[1]*i,i=A),seq(vars_in[2]*j, j=A)})];
	if type(rt_in,`+`) then 
		real_final := check_bound_for_P([op(op(rt_in)[2])], op(rt_in)[1],vars_in);
		read_out_final := Z2Intrinsic([op({op(real_final), op(A_befor)})], vars_in);
		return read_out_final;
	else	
		read_out := Z2Intrinsic(A_befor, vars_in);
		return read_out;
	end if:
end proc:
#<-----------------------------------------------------------------------------
# Function: {}
# Briefly: { }
# Calling sequence:
# {}
# Input:
# { }
# { }
# { }
# Output:
# { }
#>-----------------------------------------------------------------------------
MonomialMaker:= proc (d,V) 
options operator, arrow; 
	op(randpoly(V, degree = d, dense, homogeneous, coeffs = proc () 1 end proc)); 
end proc:
#<-----------------------------------------------------------------------------
# Function: {}
# Briefly: { }
# Calling sequence:
# {}
# Input:
# { }
# { }
# { }
# Output:
# { }
#>-----------------------------------------------------------------------------
check_bound_for_P := proc(V_in, Itr_in, vars_in)
local homogn_monoms_table,flag,empty_plate,i,vec_part,l_tab,l_v,int_part,lm_I,lm_tab,internal_flg,mult_in:
	homogn_monoms_table := table();
	flag := true;
	empty_plate := NULL;
	for i from 0 to 5 do
		homogn_monoms_table[i] := MonomialMaker(i,vars_in);
	end do:
	for i from 1 to 5 while flag do #the upper bound here is considered to be 5
		vec_part := [seq(seq(l_v*l_tab, l_tab=[homogn_monoms_table[i]]),l_v=V_in)];
		int_part := [seq(seq(lm_I*lm_tab, lm_tab=[homogn_monoms_table[i-1]]),lm_I=Itr_in)];
		internal_flg := true;
		for mult_in in vec_part while internal_flg do
			if Z2MoraNFM(mult_in,int_part, vars_in)<>0 then
				internal_flg := false;
				empty_plate := 	empty_plate, seq(seq(j*k, j=[homogn_monoms_table[i+1]]),k=V_in);	
			end if:	
		end do:
		if internal_flg then
			flag:=false;
			empty_plate := 	empty_plate, op(vec_part);
		end if:
	end do:	
	return([empty_plate]);
end proc:
#<-----------------------------------------------------------------------------
# Function: {}
# Briefly: { }
# Calling sequence:
# {}
# Input:
# { }
# { }
# { }
# Output:
# { }
#>-----------------------------------------------------------------------------
Z2T := proc(h_in, vars_in::list)
local rt_in, A, i, STB,diff_begin,l, vector_extra, j, T_out:
	rt_in := Z2RT(h_in, vars_in);
	if type(rt_in,`+`) then
		A := [op(rt_in)];
		A := [seq(op(i),i=A)];
	else
		A := rt_in;
	end if:
	STB := Z2STD(A, vars_in);
	diff_begin := diff(h_in, vars_in[2]);
	l := 0;
	while Z2MoraNFM(vars_in[2]^l*diff_begin, STB,vars_in )<>0 do
		l := l+1;
	end do:
	l := l-1;
	vector_extra := {seq(vars_in[2]^j*diff_begin, j=0..l)};
	T_out := rt_in+vector_extra;
	return(T_out);
end proc:
#<-----------------------------------------------------------------------------
# Function: {}
# Briefly: { }
# Calling sequence:
# {}
# Input:
# { }
# { }
# { }
# Output:
# { }
#>-----------------------------------------------------------------------------
Extract_intrinsic := proc(L_in, Vecrt_in, vect_in, vars)
local rm_first,if_check_passed_first, l_first,ready_out,rm_second, if_check_passed_second,l_second, send_out,after_ready,Vecrt,vect:
	Vecrt := [seq(expand(i), i=Vecrt_in)];
	vect :=  [seq(expand(j), j=vect_in)];
	rm_first := RemoveFirstVar(L_in,vars);
	#if_check_passed_first := true;
	#for l_first in rm_first while if_check_passed_first=true do
		#if SNF(l_first,L_in,[op(Vecrt),op(vect)],vars)<>0 then
			#if_check_passed_first := false;			
		#end if:
	#end do:
	#if if_check_passed_first =false then
		#ready_out := L_in;
	#else
		rm_second :=RemoveSecondVar(rm_first,vars);
		after_ready := InnerRemove(rm_second,vars);
		if_check_passed_second := true;	
		for l_second in after_ready while if_check_passed_second=true do
			if SNF(l_second,L_in,[op(Vecrt),op(vect)],vars)<>0 then
				if_check_passed_second := false;
			end if:
		end do:
		if if_check_passed_second=false then
			ready_out := L_in;
		else
			ready_out := after_ready;
		end if:	
	#end if:
	send_out :={seq(Z2MoraNFM(i,ready_out,vars), i=[op(Vecrt), op(vect)])} minus {0};
	return([ready_out,send_out]);	
end proc:
#<-----------------------------------------------------------------------------
# Function: {}
# Briefly: { }
# Calling sequence:
# {}
# Input:
# {L_in : candidate for intrinsic part }
# { vars_in : variables}
# { }
# Output:
# { }
#>-----------------------------------------------------------------------------
RemoveFirstVar := proc(L_in, vars_in)
local F, ready_plate, elem:
	F := L_in;
	ready_plate := NULL;
	for elem in F do
		if degree(elem, {vars_in[1]})>1 then
			ready_plate := 	ready_plate, (elem/vars_in[1]);
		else
			ready_plate := ready_plate, elem;	
		end if:
	end do:
	return([ready_plate]);
end proc:
#<-----------------------------------------------------------------------------
# Function: {}
# Briefly: { }
# Calling sequence:
# {}
# Input:
# { }
# { }
# { }
# Output:
# { }
#>-----------------------------------------------------------------------------
RemoveSecondVar := proc(L_in, vars_in)
local F, ready_plate, elem:
	F := L_in;
	ready_plate := NULL;
	for elem in F do
		if degree(elem, {vars_in[2]})>1 then
			ready_plate := 	ready_plate, (elem/vars_in[2]);
		else
			ready_plate := ready_plate, elem;	
		end if:
	end do:
	return([ready_plate]);
end proc:
#<-----------------------------------------------------------------------------
# Function: {}
# Briefly: { }
# Calling sequence:
# {}
# Input:
# { }
# { }
# { }
# Output:
# { }
#>-----------------------------------------------------------------------------
InnerRemove := proc(L_in, vars_in)
local elem, elem_new, F, G_in:
	G_in := {op(L_in)};
	for elem in G_in do
		F := {op(G_in)} minus {elem};
		for elem_new in F do
			if degree(elem_new, {vars_in[1]})>= degree(elem, {vars_in[1]}) and degree(elem_new,{vars_in[2]})>= degree(elem, {vars_in[2]}) then 
		G_in := {op(G_in)} minus {elem_new};
			end if:
		end do:
	end do:
	return(G_in);
end proc:
#<-----------------------------------------------------------------------------
# Function: {}
# Briefly: { }
# Calling sequence:
# {}
# Input:
# { }
# { }
# { }
# Output:
# { }
#>----------------------------------------------------------------------------
IntInterReduce:=proc(RR,vars)
local R,h,H,r;
#option trace;
	R:=subs(0=NULL,RR);
	H:=NULL;
	while nops(R)<>0 do
		r:=R[1];
		R:=R[2..-1];
		h:=IntDivAlg(r,[H,op(R)],vars);
		if h<>0 then
			H:=H,h;
		fi;
	od;
	RETURN([H]);
end:

IntDivAlg:=proc(f,FF,vars)
#option trace;
local p,r,n,T,i,flag,F;
	p:=f;
	r:=0;
	F:=subs(0=NULL,FF);
	n:=nops(F);
	T:=plex(op(vars));
	while p<>0 do
		 i:=1;
		 flag:=false;
		 while not flag and i<=n do 
			if Z2LM(p,vars)=Z2LM(F[i],vars) then
				 p:=simplify(p-F[i]/LeadingCoefficient(Z2LT(F[i],vars),T)*LeadingCoefficient(Z2LT(p,vars),T));
				 flag:=true;
			else
				 i:=i+1;
			fi;
		 od;
		 if not flag then
			r:=r+LeadingCoefficient(Z2LT(p,vars),T)*Z2LM(p,vars);
			p:=simplify(p-LeadingCoefficient(Z2LT(p,vars),T)*Z2LM(p,vars));
		fi;
	od;
	if r<>0 then
		 r:=r/LeadingCoefficient(Z2LT(r,vars),T);
	fi;
	RETURN(r);    
end:
#<-----------------------------------------------------------------------------
# Function: {}
# Briefly: { }
# Calling sequence:
# {}
# Input:
# { }
# { }
# { }
# Output:
# { }
#>----------------------------------------------------------------------------
SNF:=proc(f,F,V,vars)
local r;
	r:=Z2MoraNFM(f,F,vars);
	r:=If_belong_to_vspace(r,V,vars);
	return(r);
end:
#<-----------------------------------------------------------------------------
# Function: {}
# Briefly: { }
# Calling sequence:
# {}
# Input:
# { }
# { }
# { }
# Output:
# { }
# {this function need to be modified. Now it works for only Golubitsky's example}
#>----------------------------------------------------------------------------
If_belong_to_vspace:=proc(f_in, L_in, vars_in)
local empty_plate,elem,l_monoms,L_new,befor_matrix,f_new,f_matrix,final_out,real_final, i, j,rank_in :
	if type(f_in, `integer`) and nops(L_in)=1 then
		if type(L_in[1],`integer`) then
			return(0);
		end if:
	elif not type(f_in, `integer`) and nops(L_in)=1 then
		if type(L_in[1],`integer`) then
			return(1);
		end if:
	end if:
	empty_plate := NULL;
	for elem in L_in do
		if type(elem, `+`) then
			empty_plate := empty_plate, op(elem);
		else
			empty_plate := empty_plate, elem;
		end if:
	end do:
	l_monoms := [op({seq(Z2LM(j, vars_in),j={empty_plate})})];
	L_new := subs([seq(l_monoms[i]=y[i], i=1..nops(l_monoms))], L_in);
	befor_matrix := simplify(subs([seq(y[i]=UnitVector(i,nops(l_monoms)),i=1..nops(l_monoms))],L_new));
	f_new := subs([seq(l_monoms[i]=y[i], i=1..nops(l_monoms))], f_in);
	f_matrix := simplify(subs([seq(y[i]=UnitVector(i,nops(l_monoms)), i=1..nops(l_monoms))],f_new));
	final_out := [op(befor_matrix),f_matrix];
	real_final := convert(final_out, Matrix);
	#return(Determinant(real_final));
	rank_in := Rank(real_final);
	if evalb(rank_in=nops(final_out)) then
		return(1);
	else
		return(0);
	end if:	
end proc:
#<-----------------------------------------------------------------------------
# Function: {}
# Briefly: { }
# Calling sequence:
# {}
# Input:
# { }
# { }
# { }
# Output:
# { }
#>----------------------------------------------------------------------------
If_belong_to_vspace_perp:=proc(f_in, L_in, vars_in)
local empty_plate,elem,l_monoms,L_new,befor_matrix,f_new,f_matrix,final_out,real_final, i, j,rank_in,op_f,candid_to_add :
	if type(f_in, `+`) then	
		op_f := {op(f_in)};
	else
		op_f := f_in;
	end if:
	if type(f_in, `integer`) and nops(L_in)=1 then
		if type(L_in[1],`integer`) then
			return(0);
		end if:
	elif not type(f_in, `integer`) and nops(L_in)=1 then
		if type(L_in[1],`integer`) then
			return(1);
		end if:
	end if:
	empty_plate := NULL;
	for elem in L_in do
		if type(elem, `+`) then
			empty_plate := empty_plate, op(elem);
		else
			empty_plate := empty_plate, elem;
		end if:
	end do:
	l_monoms := [op({seq(Z2LM(j, vars_in),j={empty_plate})})];
	candid_to_add := {seq(Z2LM(i, vars_in),i=[op_f])};
	if not candid_to_add subset {op(l_monoms)} then
		l_monoms :={op(l_monoms), op(candid_to_add)}; 
	end if:
	L_new := subs([seq(l_monoms[i]=y[i], i=1..nops(l_monoms))], L_in);
	befor_matrix := simplify(subs([seq(y[i]=UnitVector(i,nops(l_monoms)),i=1..nops(l_monoms))],L_new));
	f_new := subs([seq(l_monoms[i]=y[i], i=1..nops(l_monoms))], f_in);
	f_matrix := simplify(subs([seq(y[i]=UnitVector(i,nops(l_monoms)), i=1..nops(l_monoms))],f_new));
	final_out := [op(befor_matrix),f_matrix];
	real_final := convert(final_out, Matrix);
	#return(Determinant(real_final));
	rank_in := Rank(real_final);
	if evalb(rank_in=nops(final_out)) then
		return(1);
	else
		return(0);
	end if:	
end proc:
#<-----------------------------------------------------------------------------
# Function: {}
# Briefly: { }
# Calling sequence:
# {}
# Input:
# { }
# { }
# { }
# Output:
# { }
#>----------------------------------------------------------------------------
SPERP:= proc (ff, V) 
#option trace;
local N,T,SortFun,II,q,MM,SB;
II := Z2S(ff, V);
SB:=Z2STD(II,V);   
N:=Z2NSet([op(Z2LM(SB, V))], V);
return(N);
end:
#<-----------------------------------------------------------------------------
# Function: {}
# Briefly: { }
# Calling sequence:
# {}
# Input:
# { }
# { }
# { }
# Output:
# { }
#>----------------------------------------------------------------------------
PPERP:= proc (ff, V) 
#option trace;
local N,T,SortFun,II,q,MM,SB;
II := Z2P(ff, V);
SB:=Z2STD(II,V);   
N:=Z2NSet([op(Z2LM(SB, V))], V);
return(N);
end:
#<-----------------------------------------------------------------------------
# Function: {}
# Briefly: { }
# Calling sequence:
# {}
# Input:
# { }
# { }
# { }
# Output:
# { }
#>----------------------------------------------------------------------------
IntrinsicGen:=proc(h,vars)
local itr_in :
	itr_in := Z2S(h, vars);
	return(itr_in);
end proc:
#<-----------------------------------------------------------------------------
# Function: {}
# Briefly: { }
# Calling sequence:
# {}
# Input:
# { }
# { }
# { }
# Output:
# { }
#>----------------------------------------------------------------------------
Z2Normalform := proc(g_in, vars_in)
local g, vars, high_order, Sperp, Pperp, A, C, B, g0, Modifiedg, gterms, Eqs,flag, d,c,E,S2,s,ss :
	g:=g_in;
	vars := vars_in;
	high_order := Z2P(g, vars);
	g:=NormalForm(g,high_order,plex(op(vars)));
	Sperp:=SPERP(g, vars); 
	Pperp:=PPERP(g,vars);
	A:={op(Pperp)} minus {op(Sperp)};
	C:={op(IntrinsicGen(g, vars))};
	B :=A minus C;
	if B={} then
		RETURN(g);
	fi;
	g0:=g;
	g:=subs(vars[1]=a*vars[1]+b*vars[2],g);
	Modifiedg:=g;
	gterms:=NULL;
	Eqs:=NULL;
	while g<>0 do
		gterms:=gterms,LeadingCoefficient(g,plex(op(vars)))*LeadingMonomial(g,plex(op(vars)));
		g:=simplify(g-LeadingCoefficient(g,plex(op(vars)))*LeadingMonomial(g,plex(op(vars))));
		 if LeadingMonomial(g,plex(op(vars)))in B then
			Eqs:=Eqs,LeadingCoefficient(g,plex(op(vars)));
		fi;
	od;
	g:=Modifiedg;
	Eqs:=[Eqs];
	flag:=true;
	d:=nops(Eqs);
	while d>0 and flag do
		C:=choose(nops(Eqs),d);
		for c in C while flag do 
			 E:=[seq(Eqs[i] , i=c)];
			S2:=[solve(E)];
			for s in S2 while flag do
				if (Im(eval(a,s))=0 or type(eval(a,s),symbol)) and (Im(eval(b,s))=0 or type(eval(b,s),symbol)) and eval(a,s)<>0 then
					ss:=s;
					flag:=false;
				fi;
			od;
		 od;
		if flag then
			d:=d-1;
		 fi;
	od;
	g:=expand(subs(ss,g));
	RETURN(subs(a=1,g));
end proc:
#<-----------------------------------------------------------------------------
# Function: {}
# Briefly: { }
# Calling sequence:
# {}
# Input:
# { }
# { }
# { }
# Output:
# { }
#>----------------------------------------------------------------------------
ready_UniversalUnfolding := proc(g_in, vars_in)
local complement_out, G, g, vars:
	g := simplify((g_in)/vars_in[1]);
	vars := [u, vars_in[2]];
	g := algsubs(vars_in[1]^2=u, g);
	G := Z2UniversalUnfolding(g, vars);
	G := algsubs(u=vars_in[1]^2, G);
	G := expand(vars_in[1]*G);
	return(G);
end proc:

Z2UniversalUnfolding := proc(g, vars)
local complement_out, G:
	complement_out := Z2TangentPerp(g, vars);
	G:=g+add(alpha[i]*complement_out[i],i=1..nops(complement_out));
	return(G);
end proc:
#<-----------------------------------------------------------------------------
# Function: {}
# Briefly: { }
# Calling sequence:
# {}
# Input:
# { }
# { }
# { }
# Output:
# { }
#>-----------------------------------------------------------------------------
Z2TSimplified := proc(f, vars)
local T_part, nop_T, final_T:
	T_part := Z2T(f, vars);
	nop_T := [op(T_part)];
	if nops(nop_T)=3 then 
		nop_T := Extract_intrinsic(nop_T[1], [op(nop_T[2])], [op(nop_T[3])], vars); 	
	elif nops(nop_T)=2 then
		nop_T := Extract_intrinsic(nop_T[1], [], [op(nop_T[2])], vars); 
	elif nops(nop_T)=1 then
		nop_T := Extract_intrinsic(nop_T[1], [], [], vars); 	
	end if:
	if nops(nop_T)=2 and nops(nop_T[2])=0 then
		final_T := nop_T[1];
	else 
		final_T := add(j, j=nop_T);
	end if:
	return(final_T);
end proc:
#<-----------------------------------------------------------------------------
# Function: {}
# Briefly: { }
# Calling sequence:
# {}
# Input:
# { }
# { }
# { }
# Output:
# { }
#>----------------------------------------------------------------------------
Z2TangentPerp := proc(f, vars)
local T_part, set_in, N, s_basis,ABS,H,h,RNF,nop_T,N_ready:

	T_part := Z2T(f, vars);
	nop_T := [op(T_part)];
	if nops(nop_T)=3 then 
		nop_T := Extract_intrinsic(nop_T[1], [op(nop_T[2])], [op(nop_T[3])], vars); 	
	elif nops(nop_T)=2 then 
		nop_T := Extract_intrinsic(nop_T[1], [], [op(nop_T[2])], vars); 
	elif nops(nop_T)=1 then
		nop_T := Extract_intrinsic(nop_T[1], [], [], vars); 	
	end if: 
	if nops(nop_T)=2 and nops(nop_T[2])=0 then 
		N:=Z2NSet([seq(i, i=nop_T[1])], vars);
		N_ready := N;
	elif nops(nop_T)=2 and nops(nop_T[2])=1 and type(op(nop_T[2]),`realcons`) then 
		N:=Z2NSet([seq(i, i=nop_T[1])], vars);#just modified it
		N_ready := {op(N)} minus {op(nop_T[2])/LeadingCoefficient(op(nop_T[2]), plex(op(vars)))};
	elif nops(nop_T)=2 then
		N := Z2NSet([seq(i, i=nop_T[1])], vars);
		N_ready :=Simplification_vector_ideal(N,nop_T[2],vars);
	else 
		N := Z2NSet([seq(i, i=nop_T[1])], vars);
		N_ready :=Simplification_vector_ideal(N,{op(nop_T[2]),op(nop_T[3])},vars);		
	end if:
	return(N_ready); 
end proc:
#<-----------------------------------------------------------------------------
# Function: {}
# Briefly: { }
# Calling sequence:
# {}
# Input:
# { }
# { }
# { }
# Output:
# { }
#>----------------------------------------------------------------------------
Simplification_vector_ideal := proc(NSet_in, vector_in, vars)
local N_in, vec_in, empty_plate, elem:
	N_in := NSet_in;
	vec_in := vector_in;
	if {1} subset {op(N_in)} and {1} subset vec_in then
			N_in := {op(N_in)} minus {1};
			vec_in := vec_in minus {1};
	end if:
	empty_plate := NULL;
	if {1} subset {op(N_in)} then
		N_in := {op(N_in)} minus {1};
		empty_plate := empty_plate, 1;
	end if:
	for elem in N_in do
		if If_belong_to_vspace_perp(elem,[op(vec_in)],vars)=1 then
			empty_plate := 	empty_plate, elem;
			vec_in := {op(vec_in), elem};
		end if:
	end do:
	return ([empty_plate]);
end proc:
#<-----------------------------------------------------------------------------
# Function: {}
# Briefly: { }
# Calling sequence:
# {}
# Input:
# { }
# { }
# { }
# Output:
# { }
#>----------------------------------------------------------------------------
UniversalUnfoldingold := proc(g_in, vars_in, {symmetry:='Z2'})
	if symmetry='Z2' then
		return(ready_UniversalUnfolding(g_in, vars_in));
	end if:
end proc:
UniversalUnfolding := proc()
local n_form, m_taylor:
	if evalb(nargs=5 and args[4]=normalform and lhs(args[5])='symmetry' and rhs(args[5])='Z2') then
		m_taylor := mtaylor(args[1], args[2], args[3]);
		n_form := Normalform(m_taylor, args[2], args[5]);
		return(ready_UniversalUnfolding(n_form, args[2]));
	elif evalb(nargs=4 and lhs(args[4])='symmetry' and rhs(args[4])='Z2') then 
		n_form := Normalform(args[1], args[2], args[4]);
		return(ready_UniversalUnfolding(n_form, args[2]));
	else
		return(ready_UniversalUnfolding(args[1], args[2]));
	end if:
end proc:
#<-----------------------------------------------------------------------------
# Function: {}
# Briefly: { }
# Calling sequence:
# {}
# Input:
# { }
# { }
# { }
# Output:
# { }
#>----------------------------------------------------------------------------
ready_AlgObjects := proc(g_in, vars_in)
	local g, vars, RT_ready_first, RT_ready_second, RT_ready_final, i, P_ready_first, P_ready_second, P_ready_final, j, k, S_ready_first, S_ready_second, S_ready_final, jj, T_ready_first, T_ready_second, T_ready_final, ideal_T, break_T,  break_in, jjj, break_RT,ideal_RT, TangPerp ,s_perp, p_perp:
	g := simplify((g_in)/(vars_in[1]));
	vars := [u, vars_in[2]];
	g := algsubs(vars_in[1]^2=u, g);
	RT_ready_first := Z2RT(g, vars);
	RT_ready_second := algsubs(u=vars_in[1]^2, RT_ready_first);
	if type(RT_ready_second,`+`) then
		break_RT := op(RT_ready_second);
		break_RT := [break_RT];
		ideal_RT := [seq(vars_in[1]*jj, jj=break_RT[1])];
		for break_in in break_RT[2..-1] do
			ideal_RT:= ideal_RT+{seq(expand(vars_in[1]*jj), jj=break_in)};
		end do:
		RT_ready_final := ideal_RT;
	else
		RT_ready_final := [seq(vars_in[1]*jj, jj=RT_ready_second)];	
	end if:
	#RT_ready_final := [seq(vars_in[1]*i, i=RT_ready_second)];
	P_ready_first := Z2P(g, vars);
	P_ready_second := algsubs(u=vars_in[1]^2, P_ready_first);
	P_ready_final := [seq(vars_in[1]*j, j=P_ready_second)];
	S_ready_first := Z2S(g, vars);
	S_ready_second := algsubs(u=vars_in[1]^2, S_ready_first);
	S_ready_final := [seq(vars_in[1]*k, k=S_ready_second)];
	T_ready_first := Z2TSimplified(g, vars);
	T_ready_second :=algsubs(u=vars_in[1]^2, T_ready_first);
	if type(T_ready_second,`+`) then
		break_T := op(T_ready_second);
		break_T := [break_T];
		ideal_T := [seq(vars_in[1]*jj, jj=break_T[1])];
		for break_in in break_T[2..-1] do
			ideal_T:= ideal_T+{seq(expand(vars_in[1]*jj), jj=break_in)};
		end do:
		T_ready_final := ideal_T;
	else
		T_ready_final := [seq(vars_in[1]*jj, jj=T_ready_second)];	
	end if:
	TangPerp := ready_TangentPerp(g_in, vars_in);
	s_perp := SPERP(g, vars);
	s_perp := algsubs(u=vars_in[1]^2, s_perp);
	s_perp := {seq(vars_in[1]*k, k=s_perp)};
	p_perp :=  PPERP(g, vars);
	p_perp := algsubs(u=vars_in[1]^2, p_perp);
	p_perp := {seq(vars_in[1]*k, k=p_perp)};
	#printf(" %1s %1s %1s %1s %1s :%1a \n", The, restricted, tangent, space, is, RT_ready_final);
	print("RT=",RT_ready_final);
	print("P=",P_ready_final);
	print("Pperp=",p_perp);
	print("S=",S_ready_final);
	print("Sperp=",s_perp);
	print("T=",T_ready_final);
	print("Tperp=",TangPerp);
	#printf(" %1s %1s %1s %1s %1s :%1a \n", The, high, order, terms, are, P_ready_final);
	#printf(" %1s %1s %1s %1s %1s :%1a \n", The, smallest, intrinsic, submodule, is, S_ready_final);
	#printf(" %1s %1s %1s %1s :%1a \n", The, tangent, space, is, T_ready_final);
	#printf(" %1s %1s %1s %1s :%1a \n", The, tangent, perp, is, TangPerp);
	
	
end proc:
#<-----------------------------------------------------------------------------
# Function: {}
# Briefly: { }
# Calling sequence:
# {}
# Input:
# { }
# { }
# { }
# Output:
# { }
#>----------------------------------------------------------------------------
AlgObjects := proc()
local m_talor:
	if evalb(nargs=4 and lhs(args[4])='symmetry' and rhs(args[4])='Z2') then
		m_talor := mtaylor(args[1], args[2], args[3]);
		m_talor := Normalform(m_talor, args[2], args[4]);
		return(ready_AlgObjects(m_talor,args[2]));
	elif evalb(nargs=3 and lhs(args[3])='symmetry' and rhs(args[3])='Z2') then
		m_talor := Normalform(args[1], args[2], args[3]);
		return(ready_AlgObjects(m_talor,args[2]));
	end if:
end proc:
#<-----------------------------------------------------------------------------
# Function: {}
# Briefly: { }
# Calling sequence:
# {}
# Input:
# { }
# { }
# { }
# Output:
# { }
#>----------------------------------------------------------------------------
TransitionSet := proc(G_in, vars::list, params_in::list, {symmetry:='Z2'})
	
	if symmetry='Z2' then
		return(Z2TransitionSet(G_in, vars, params_in));
	end if:
end proc:
#<-----------------------------------------------------------------------------
# Function: {}
# Briefly: { }
# Calling sequence:
# {}
# Input:
# { }
# { }
# { }
# Output:
# { }
#>----------------------------------------------------------------------------
ready_Normalform := proc(f_in, vars_in::list)
	local f, vars:
	f := simplify((f_in)/(vars_in[1]));
	vars := [u, vars_in[2]];
	f := algsubs(vars_in[1]^2=u, f);
	f := Z2Normalform(f, vars);
	f := algsubs(u=vars_in[1]^2, f);
	f := expand(vars_in[1]*f);
	return(f);
end proc:

Normalform := proc()
local m_talor:
	if evalb(nargs=4 and lhs(args[4])='symmetry' and rhs(args[4])='Z2') then
		m_talor := mtaylor(args[1], args[2], args[3]);
		return(ready_Normalform(m_talor,args[2]));
	elif evalb(nargs=3 and lhs(args[3])='symmetry' and rhs(args[3])='Z2') then
		return(ready_Normalform(args[1],args[2]));
	end if:
end proc:
#<-----------------------------------------------------------------------------
# Function: {}
# Briefly: { }
# Calling sequence:
# {}
# Input:
# { }
# { }
# { }
# Output:
# { }
#>----------------------------------------------------------------------------
ready_TangentPerp := proc(f_in, vars_in)
local f, vars:
	f := simplify((f_in)/(vars_in[1]));
	vars := [u, vars_in[2]];
	f := algsubs(vars_in[1]^2=u, f);
	f := Z2TangentPerp(f, vars);
	f := algsubs(u=vars_in[1]^2, f);
	f := {seq(expand(vars_in[1]*i), i=f)};
	return(f);
end proc:

TangentPerp := proc()
local m_talor:
	if evalb(nargs=4 and lhs(args[4])='symmetry' and rhs(args[4])='Z2') then
		m_talor := mtaylor(args[1], args[2], args[3]);
		return(ready_TangentPerp(m_talor,args[2]));
	elif evalb(nargs=3 and lhs(args[3])='symmetry' and rhs(args[3])='Z2') then
		return(ready_TangentPerp(args[1],args[2]));
	end if
end proc:
#<-----------------------------------------------------------------------------
# Function: {}
# Briefly: { }
# Calling sequence:
# {}
# Input:
# { }
# { }
# { }
# Output:
# { }
#>----------------------------------------------------------------------------
Z2RecognitionProblem := proc(g_in, vars_in::list)
local NF_in, S_perp, zero_condition, f, v, q,  non_zero_condition, S_in, vars:
		NF_in := ready_Normalform(g_in, vars_in);
		NF_in := simplify((NF_in)/(vars_in[1]));
		vars := [u, vars_in[2]];
		NF_in := algsubs(vars_in[1]^2=u, NF_in);
		S_perp := SPERP(NF_in, vars);
		S_perp := algsubs(u=vars_in[1]^2, S_perp);
	        S_perp := {seq(vars_in[1]*k, k=S_perp)};
		S_in := Z2S(NF_in, vars);
		S_in := algsubs(u=vars_in[1]^2, S_in);
		S_in := [seq(vars_in[1]*k, k=S_in)];
		zero_condition := NULL;	
		if vars_in[1] in S_perp then
			zero_condition := zero_condition, Diff(f, vars_in[1])=0;
			S_perp := [op({op(S_perp)} minus {x})];
			zero_condition := [zero_condition, seq(Diff(f,vars_in[1]$degree(v,vars_in[1]),vars_in[2]$degree(v,vars_in[2]))=0,v in S_perp), f(-vars_in[1], vars_in[2])+f(vars_in[1], vars_in[2])=0];
		end if:
		non_zero_condition := [seq(Diff(f,vars_in[1]$degree(q,vars_in[1]),vars_in[2]$degree(q,vars_in[2]))<>0, q in S_in)];
		printf(" %1s %1s %1s :%1a \n", Zero, Conditions, are, zero_condition);
		printf(" %1s %1s %1s :%1a \n", NonZero, Conditions, are, non_zero_condition);
end proc:
#<-----------------------------------------------------------------------------
# Function: {}
# Briefly: { }
# Calling sequence:
# {}
# Input:
# { }
# { }
# { }
# Output:
# { }
#>----------------------------------------------------------------------------
RecognitionProblem := proc()
	if  evalb(nargs=3 and lhs(args[3])='symmetry' and rhs(args[3])='Z2') then
		return(Z2RecognitionProblem(args[1], args[2]));
	end if:
end proc:
#<-----------------------------------------------------------------------------
# Function: {}
# Briefly: { }
# Calling sequence:
# {}
# Input:
# { }
# { }
# { }
# Output:
# { }
#>----------------------------------------------------------------------------
Z2_recognition_universal_unfolding:=proc(h,vars)
#option trace;
local c,ET,G,A,B,tt,d,C,K,z,W,N,F,g,gg,MM,k,E,hh,HH;
	c := ComplemenT(PRNEW(h,vars),vars);
	d := SPERP(h, vars);
	ET := PRTT2(h,vars);
	B := [diff(g(op(vars)), `$`(vars[1], 1)), diff(g(op(vars)), `$`(vars[2], 1))];
	A := NULL;
	for tt in B do 
		if {op(FINDPOWER(DERIVATIVE(c,tt,vars),DERIVATIVE(d,g(op(vars)),vars)))}<>{0} then 
			A := A,tt;
		fi;
	od;
	C := [A, seq(diff(G(vars[1], vars[2], seq(alpha[j], j = 1 .. nops(ET))), `$`(i, 1)), i = [seq(alpha[j], j = 1 .. nops(ET))])];
	K := NULL;
	for z in C do
		 K := K, FINDPOWER(DERIVATIVE(c, z,vars), DERIVATIVE(d, g(op(vars)),vars));
	od;
	W := subs([1 = vars[1], 2 = vars[2], 3 = alpha[1], 4 = alpha[2], 5 = alpha[3], D = g, g = 0, G = 0], [K]);
	N := NULL;
	for F in W do
		A := NULL;
		for gg in F do
			if gg=0 then
				A := A, gg;
			else
				A := A, op(0, gg);
			fi;
		od;
		N := N, [A];
	od;
	[N];
	MM := NULL;
	for k in [N] do
		E := NULL;
		for hh in k do
			if hh=0 then
				E := E, hh;
			elif {op( op(0,hh))}subset {op(vars)} then
				E := E, hh;
			else
				HH := subs(g = G, hh);
				E := E, HH;
		         fi;
		od;
		MM := MM, [E];
	od;
	[MM];
	return(det(convert([MM], Array)) <> 0);
    end:
#<-----------------------------------------------------------------------------
# Function: {}
# Briefly: { }
# Calling sequence:
# {}
# Input:
# { }
# { }
# { }
# Output:
# { }
#>----------------------------------------------------------------------------

DERIVATIVE:=proc(NN,g,vars)
#option trace;
local MM,t,N,W;
	MM := NULL;
	for t in NN do
		if nops([op(t)])=1 and op(t)=1  then
			MM := MM, g;
		elif nops([op(t)])=1 and op(t)<>1  then
			MM := MM, diff(g, [`$`(t, degree(t))]);
		elif nops([op(t)])=2 and type([op(t)][2],integer)=true then
			MM := MM, diff(g, [`$`([op(t)][1], degree(t))]);
		elif nops([op(t)])=2 and type([op(t)][2],integer)=false then
			MM := MM, diff(g, `$`([op(t)][1], degree([op(t)][1])), `$`([op(t)][2], degree([op(t)][2])));
		fi;
	od;
	N := convert([MM], D);
	W := subs([vars[1] = 0, vars[2] = 0], N);
end:

FINDPOWER:=proc(L,K)
#option trace;
local Q,C,t;
	Q := L;
	C := K;
	for t in Q do
		if nops([op(t)])=1 then
			if  t in C  then	
				Q := subs(t = 0, Q);
			fi;
		elif nops([op(t)])=2 and  type([op(t)][1],integer)=true then
			if [op(t)][1]=0 and [op(t)][2]=0 and t in C then
				Q := subs(t = 0, Q);
			elif [ op(t)][2] in C then 
				Q := subs(t = 0, Q);
			fi;
		fi;
	od;
	Q;
end:
