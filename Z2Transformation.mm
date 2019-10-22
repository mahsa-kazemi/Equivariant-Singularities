read "Z2Bifurcation.mm":
with(Groebner):
with(ListTools):
with(SolveTools):
#<-----------------------------------------------------------------------------
# Function: {  }
# Description: { }
# Calling sequence:
# {  }
# Input:
# {}
# { }
# Output:
# {}
#>-----------------------------------------------------------------------------
Take_list := proc(Monom_in, L_in, vars_in)
local elem:
	for elem in Monom_in do
		if Z2MoraNFM(elem, L_in, vars_in)<>0 then
			return(false);
		end if:
	end do:
	return(true);
end proc:

High_order:= proc(M_in, vars)
local i:

	for i from 1 to 10 do
		if Take_list([MonomialMaker(i,vars)], M_in, vars) then
			return(i);
		end if:
	end do:
	return(i);
end proc:
#<-----------------------------------------------------------------------------
# Function: {  }
# Description: { }
# Calling sequence:
# {  }
# Input:
# {}
# { }
# Output:
# {}
#>-----------------------------------------------------------------------------
PerturbToUnfold:=proc(f_in,vars_in::list, paramsPerturb::list)
#option trace;
local start_poly, start_poly_subs, start_poly_monoms,f,p,g,paramsUnfold,g_poly,emp_plate,elem,want_in,near_in,near_final,final_output,
we_need,par_need,S,X,h,S0,B1,ff,fff,LL,A,t,i,B,k,KAZ,C,z,monom,coco_out,flag,ModifiedBis,Solve_part,DD,r,DDD,DDDD,MARI,ASADI,j,MAHSA,MAH,a,wow,ava,dovo,sevo,charo,na,lam,bom,q1,q2,q3,outer_in,empty_new,part_in,fill_new,right_new,add_fill_new,final_list,rem_out,f_new,co_out,rel_in,hey,final_outputy,for_final, jjj,jj, other_side, high_order_ready, vars_test, g_nf :
	
	f :=subs([seq(ind=0, ind=paramsPerturb)],f_in);
	f := simplify((f)/(vars_in[1]));
	vars := [u, vars_in[2]];
	f := algsubs(vars_in[1]^2=u, f);
	high_order_ready := Z2P(f, vars);
	p := High_order(high_order_ready, vars);
	g_nf := Z2Normalform(f, vars);
	g := Z2UniversalUnfolding(g_nf,  vars);print("UniUnfold",g);
	paramsUnfold := [op(indets(g) minus {op(vars)})];
	final_output := algsubs(vars_in[1]^2=u,simplify((f_in)/(vars_in[1])));
	we_need := indets(final_output);
	par_need := we_need minus {op(vars)};

	if nops(par_need)=1 then
		S:=add(add(add(a[i,j,k]*vars[1]^i*vars[2]^j*par_need[1]^k, k=0..p-1-i-j),j=0..p-1-i),i=0..p-1);print("S",S);
		X:=add(add(add(b[i,j,k]*vars[1]^i*vars[2]^j*par_need[1]^k, k=0..p-1-i-j),j=0..p-1-i),i=0..p-1);print("X",X);
		#F_lam := add(c[i]*vars[2]^i, i=1..p-1);
		h:=mtaylor(add(add(add(a[i,j,k]*vars[1]^i*vars[2]^j*par_need[1]^k, k=0..p-1-i-j),j=0..p-1-i),i=0..p-1)*subs([vars[1]=add(add(add(b[i,j,k]*vars[1]^i*vars[2]^j*par_need[1]^k, k=0..p-1-i-j),j=0..p-1-i),i=0..p-1)],final_output ),vars,p+4);#p+4
	elif  nops(par_need)=2 then
		S:=add(add(add(add(a[i,j,k,l]*vars[1]^i*vars[2]^j*par_need[1]^k*par_need[2]^l,l=0..p-1-k-j-i), k=0..p-1-i-j),j=0..p-1-i),i=0..p-1);
		X:=add(add(add(add(b[i,j,k,l]*vars[1]^i*vars[2]^j*par_need[1]^k*par_need[2]^l,l=0..p-1-k-j-i), k=0..p-1-i-j),j=0..p-1-i),i=0..p-1);	      #F_lam := add(c[i]*vars[2]^i, i=1..p-1);
		h:=mtaylor(add(add(add(add(a[i,j,k,l]*vars[1]^i*vars[2]^j*par_need[1]^k*par_need[2]^l,l=0..p-1-k-j-i), k=0..p-1-i-j),j=0..p-1-i),i=0..p-1)*subs([vars[1]=add(add(add(add(b[i,j,k,l]*vars[1]^i*vars[2]^j*par_need[1]^k*par_need[2]^l,l=0..p-1-k-j-i), k=0..p-1-i-j),j=0..p-1-i),i=0..p-1)],final_output ),vars,p+5);#p+5
	elif  nops(par_need)=3 then
			S:=add(add(add(add(add(a[i,j,k,l,m]*vars[1]^i*vars[2]^j*par_need[1]^k*par_need[2]^l*par_need[3]^m,m=0..p-1-l-k-j-i),l=0..p-1-k-j-i), k=0..p-1-i-j),j=0..p-1-i),i=0..p-1);
			X:=add(add(add(add(add(b[i,j,k,l,m]*vars[1]^i*vars[2]^j*par_need[1]^k*par_need[2]^l*par_need[3]^m,m=0..p-1-l-k-j-i),l=0..p-1-k-j-i), k=0..p-1-i-j),j=0..p-1-i),i=0..p-1);
			h:=mtaylor(add(add(add(add(add(a[i,j,k,l,m]*vars[1]^i*vars[2]^j*par_need[1]^k*par_need[2]^l*par_need[3]^m,m=0..p-1-l-k-j-i),l=0..p-1-k-j-i), k=0..p-1-i-j),j=0..p-1-i),i=0..p-1)*subs(vars[1]=add(add(add(add(add(b[i,j,k,l,m]*vars[1]^i*vars[2]^j*par_need[1]^k*par_need[2]^l*par_need[3]^m,m=0..p-1-l-k-j-i),l=0..p-1-k-j-i), k=0..p-1-i-j),j=0..p-1-i),i=0..p-1),final_output ),vars,p+3);	
	elif  nops(par_need)=4 then
			S:=add(add(add(add(add(add(a[i,j,k,l,m,n]*vars[1]^i*vars[2]^j*par_need[1]^k*par_need[2]^l*par_need[3]^m*par_need[4]^n,n=0..p-1-m-l-k-j-i),m=0..p-1-l-k-j-i),l=0..p-1-k-j-i), k=0..p-1-i-j),j=0..p-1-i),i=0..p-1);
			X:=add(add(add(add(add(add(b[i,j,k,l,m,n]*vars[1]^i*vars[2]^j*par_need[1]^k*par_need[2]^l*par_need[3]^m*par_need[4]^n,n=0..p-1-m-l-k-j-i),m=0..p-1-l-k-j-i),l=0..p-1-k-j-i), k=0..p-1-i-j),j=0..p-1-i),i=0..p-1);
			h:=mtaylor(add(add(add(add(add(add(a[i,j,k,l,m,n]*vars[1]^i*vars[2]^j*par_need[1]^k*par_need[2]^l*par_need[3]^m*par_need[4]^n,n=0..p-1-m-l-k-j-i),m=0..p-1-l-k-j-i),l=0..p-1-k-j-i), k=0..p-1-i-j),j=0..p-1-i),i=0..p-1)*subs(vars[1]=add(add(add(add(add(add(b[i,j,k,l,m,n]*vars[1]^i*vars[2]^j*par_need[1]^k*par_need[2]^l*par_need[3]^m*par_need[4]^n,n=0..p-1-m-l-k-j-i),m=0..p-1-l-k-j-i),l=0..p-1-k-j-i), k=0..p-1-i-j),j=0..p-1-i),i=0..p-1),final_output),vars,p+3);	
	elif  nops(par_need)=5 then
		return(hi);
	elif nops(par_need)=0 then
		return("identity");
	end if:

	start_poly := [op(h)];
	start_poly_subs := subs([seq(i=1,i=paramsPerturb)],start_poly);
	start_poly_monoms := [seq(LeadingMonomial(j,plex(op(vars))),j=start_poly_subs)];
	g_poly := [op(g)];
	emp_plate := NULL;
	for_final := NULL;
	for elem in g_poly do 
		if indets(elem) minus {op(vars)} subset {op(paramsUnfold)} and nops(indets(elem) minus {op(vars)})<>0 then
			for_final := for_final, elem;
			emp_plate := emp_plate,subs([seq(i=1,i=paramsUnfold)],elem);#this	
		end if:
	end do;
	want_in := [op({seq(Search(new_el,start_poly_monoms),new_el=[emp_plate])} minus {0})];
	near_in := {seq(start_poly[jj],jj=want_in)};
	near_final := {op(start_poly)} minus near_in;
	final_outputy := add(hh, hh=near_final);
	S0 := subs([seq(jj=0,jj=we_need)],S);
	B1 := subs([seq(jj=0,jj=we_need)],X);
	#B11 := c1;
	ff:=collect(final_outputy, [op(we_need)],`distributed`);
	fff:=sort(ff,order = tdeg(op(we_need)), ascending);
	LL:=[op(fff)];
	A:=NULL;
	for t in LL do
		A:=A,degree(t,{op(we_need)});
	od;print("hiii",A);
	for i from 0 to max(A) do #be careful we may not have 0 always
		B[i]:=NULL;
	od;
	for k in LL do
		B[degree(k,{op(we_need)})]:=B[degree(k,{op(we_need)})],k;
	od;
	KAZ:=NULL;
	for i from min(A) to p+1 do 
		C[i]:=NULL;
		for z in [op({B[i]}minus{0})] do 
				monom:=simplify(z/LeadingCoefficient(z,plex(op(we_need))));
				coco_out :=FindCoef(monom, g, [op(we_need)]);
				C[i]:=C[i],z/monom=coco_out;
		od;
		flag:=false;
		ModifiedBis := [C[i]];
		ModifiedBis := [seq(lhs(ii)-rhs(ii), ii=ModifiedBis)];
		vars_related := {seq(op(indets(jj)),jj=ModifiedBis)};
		if nops(ModifiedBis)=0 then
			flag:=true;
		end if:
		if flag=false then
			Solve_part := ModifiedBis;
		else
			Solve_part := [];
		end if:
			DD := PolynomialSystem(ModifiedBis,vars_related,{S0 <> 0, B1 <> 0});
			#if DD={} then
			if nops([DD])=0 then
				DD := NULL;
			end if:
			if nops([DD])<>0 then 
				for t in [DD] do
					if {sign(S0)=-1} subset t then
						DD:=op({DD} minus {t});
					elif {S0=0} subset t then
						DD:=op({DD} minus {t});
					elif {B1=0} subset t then 
						DD:=op({DD} minus {t});
					fi;
				od;
			fi;
			if nops([DD])<>0 then
				for t in [DD] do
					for r in t do 
						if [op(r)][1]=S0 and type([op(r)][2],function) then 
							DD:=op({DD} minus {t});
						fi;
					od;
				od;
			fi;
			if nops([DD])<>0 then
				for t in [DD] do 
					for k in t do
						if B1=op(1,k) and type(op(2,k),realcons)=true and op(2,k)>0 or B1=op(1,k) and B1=op(2,k) then 
							DD:=t;
						fi;
					od;
				od;
				DDD:=DD;
				DDDD:=NULL;
				for t in DDD do
					if type(op(2,t),function)=true then 
						DDDD:=DDDD,op(1,t)=[allvalues(op(2,t))][1];
					elif type(op(2,t),function)=false then
						DDDD:=DDDD,t;
					fi;
				od;
				#if nops([DD])= 1 then
					#DDDD:= op(DD); print("DDDD",DDDD);
				#else
					#DDDD := op([DD][3]);print("DDDD",DDDD);
				#end if:
				
				KAZ:=KAZ,{DDDD};
				MARI:=[KAZ];
				ASADI:=DDDD;
				for j from i+1 to p+1 do 
					#if whattype(op([{ASADI}][1])[1])=set then
						#B[j]:=op(simplify(subs({ASADI}[1],[B[j]])));
					#else
						#B[j]:=op(simplify(subs([op([{ASADI}][1])],[B[j]])));    
					#fi;
					B[j] := op(simplify(subs([ASADI], [B[j]])));
				od;
			fi;
	od;
	MAHSA:=NULL;
	for t in MARI do
		MAHSA:=MAHSA,[t,{seq([op(j)][1],j=t)}];
	od;
		MAH:=[MAHSA];
	zarf := NULL;
	for ik in MAH do
		if {S0=0} subset ik[1] then
			zarf := zarf, ik;
		elif {B1=0} subset ik[1] then
			zarf := zarf, ik;
		end if:
	end do:
	MAH := [op({op(MAH)} minus {zarf})];
	for i from 1 to nops(MAH)-1 do
		a:=MAH[i];
		for t in MAH[i][1] do
			if evalb(t)=true and {[op(t)][1]} subset MAH[i+1][2] then
				 MAH[i][1]:=MAH[i][1] minus {t};
			#else
				#MAH[i][1]:=MAH[i][1];
			fi;
		od;
	od;
	wow:={seq(op(i[1]),i=MAH)};
	print(wow);
	ava:=NULL;
	dovo:=NULL;
	sevo:=NULL;
	charo:=NULL;
	for t in wow do
		if type([op(t)][2],integer) or type([op(t)][2],fraction) then
			ava:=ava,t;
		elif evalb(t)=true then
			ava:=ava,[op(t)][1]=1;
		else
			dovo:=dovo,t;
		fi;
        od;
	na:=subs([ava],[dovo]);
	for t in na do
		if type([op(t)][2],integer) or type([op(t)][2],fraction) then
			ava:=ava,t;
		else
			sevo:=sevo,t;
		fi;
	 od;
	lam:=subs([ava],[sevo]);
	for t in lam do
		if type([op(t)][2],integer) or type([op(t)][2],fraction) then
			ava:=ava,t;
		else
			charo:=charo,t;
		fi; 
	od;
	#print("hi",ava);
	#print(seq([subs([ava],[C[i]]),[C[i]]],i=5..5));
	#print("hhhhhhhhhhhhh",B[5]);
	#print(subs([ava],[seq(C[i],i=min(A)..p+1)]));
	bom:=subs([ava],[charo]);
	rel_in := near_in;
	hey := {seq(op(indets(i)), i=rel_in)} minus {op(we_need)};
	rel_in := subs([op(bom),ava],rel_in);
	rel_in := subs([seq(j=0, j=hey)],rel_in);
	rel_in := subs([seq(jjj=1,jjj=vars)],rel_in);
	other_side := subs([seq(jj=1,jj=vars)],[for_final]);
	S:=subs([op(bom),ava],S);
	q1:=indets(S) minus {op(we_need)};
	S:=subs([seq(i=0,i=q1)],S);
	X:=subs([op(bom),ava],X);
	q2:=indets(X) minus {op(we_need)};
	X:=subs([seq(i=0,i=q2)],X);#0
	h := mtaylor(expand(S*(subs(vars[1]=X,final_output))),[op(we_need)],p+2);
	#h:=expand(subs([op(bom),ava],final_outputy));
	#q3:=indets(h) minus {op(we_need)};
	#h:=expand(subs([seq(i=0,i=q3)],final_outputy));
	#outer_in := expand(S*subs(x=X,f_in));
	#return("X"=X, "S"=S,"h"=h, "relation"=outer_in);
	print("X=",X);
	print("S=",S);
	print("h= S*subs(x=X, input)",h);
	print("relation=",seq(other_side[i]=rel_in[i], i=1..nops(rel_in)));
	
end:
#<-----------------------------------------------------------------------------
# Function: {  }
# Description: { }
# Calling sequence:
# {  }
# Input:
# {}
# { }
# Output:
# {}
#<-----------------------------------------------------------------------------
# Function: {  }
# Description: { }
# Calling sequence:
# {  }
# Input:
# {}
# { }
# Output:
# {}
#>-----------------------------------------------------------------------------
SolvePart:=proc(L_in::list, parUnf::list, parPert::list)
local L_new, plate_in, elem_in, A, left_out, left_op,new_elm,indts, indts_new,B,k,final_list:
	L_new := L_in;
	plate_in := NULL;
	for elem_in in L_new do
		A := NULL;
		left_out := expand(lhs(elem_in));
		if type(left_out, `+`) then
			left_op := {op(left_out)};
			for new_elm in left_op do
				indts := indets(new_elm);
				if `intersect`(indts, {op(parPert)})={} then 
					A:= A,new_elm;
				elif `intersect`(indts, {op(parPert)})<>{} and indts minus {op(parPert)}<>{} then
					plate_in := plate_in, subs([seq(i=1,i=parPert)],new_elm)=0;
				end if:
			end do:
		else
			indts_new := indets(left_out);
			if `intersect`(indts_new, {op(parPert)})={} then 
				plate_in := plate_in, elem_in;
			elif `intersect`(indts_new, {op(parPert)})<>{} and indts_new minus {op(parPert)}<>{} then
				plate_in := plate_in, subs([seq(i=1,i=parPert)],left_out)=0;
			end if:	
		end if:	
	if nops([A])<>0 then
		plate_in := plate_in, add(j,j=[A])=rhs(elem_in);
	else
		plate_in := plate_in;
	end if:
end do:
	B := NULL;
	for k in [plate_in] do
		if evalb(lhs(k)=rhs(k))=true then
			B := B, k;
		end if:
	end do:
	final_list := op({plate_in} minus {B});
return(final_list);
end proc:
#<-----------------------------------------------------------------------------
# Function: {  }
# Description: { }
# Calling sequence:
# {  }
# Input:
# {}
# { }
# Output:
# {}
#>-----------------------------------------------------------------------------
InnerCoef := proc(f_in, L_in)
local g, elem:
	g := f;
	for elem in L_in do
		g := coeff(f, elem);
	end do:
	return(g);
end proc:
#<-----------------------------------------------------------------------------
# Function: {  }
# Description: { }
# Calling sequence:
# {  }
# Input:
# {}
# { }
# Output:
# {}
#>-----------------------------------------------------------------------------
FindCoef := proc(monom_in, func_in,vars)
local rem_out, f_new, co_out:
	if nops([op(monom_in)])=1 then
		rem_out := {op(vars)} minus {monom_in};
		f_new:=subs(rem_out[1]=0, func_in);
		co_out := coeff(f_new, monom_in);	
	elif nops([op(monom_in)])=2 and type(op(monom_in)[2],integer)=true then 
		co_out := coeff(func_in, monom_in);
	elif nops([op(monom_in)])=2 and type(op(monom_in)[2],integer)=false then 
		co_out := coeff(coeff(func_in,op(monom_in)[1]),op(monom_in)[2]);
	elif nops([op(monom_in)])>=2 then
		co_out := InnerCoef(func_in,[op(monom_in)]);
	end if:
	return(co_out);
end proc:
#<-----------------------------------------------------------------------------
# Function: {  }
# Description: { }
# Calling sequence:
# {  }
# Input:
# {}
# { }
# Output:
# {}
#>-----------------------------------------------------------------------------
Modify_B_s:=proc(B_in, unfparams_in::list)
local B_first, removed_in,elem_in, B_ready:
	B_first := {op(B_in)} minus {0};
	removed_in := NULL;
	for elem_in in B_first do
		if `intersect`(indets(rhs(elem_in)),{op(unfparams_in)})<>{} then
			removed_in := removed_in, elem_in;
		end if:
	end do:
	B_ready := B_first minus {removed_in};
	return([op(B_ready)]);
end proc:

