




#Symetry operators#

#I need Kw, the superN2symetry operator

Kzij:= proc(poly, i, j, forceVars:=1)
    local p_poly;
    p_poly:= sort(subs({z||i = z||j, z||j = z||i}, poly));
    return p_poly;
end proc:

Kscrypt_ij:= proc(poly, ijvec)
    local KsijPoly, i,j; 
    i:= ijvec[1];
    j:= ijvec[2]; 
	KsijPoly:= sort(subs({z||i = z||j, z||j = z||i, theta||i = theta||j, theta||j= theta||i, phi||i=phi||j, phi||j = phi||i}, poly)); 
    return KsijPoly;
end proc:

Ksigma_j:= proc(poly, someSet)
    local sigma_j, sigma_1, non_fixed_points, permVect, KsigmaPoly, RcycleIndex, theSubSeq, Ksigma_jPoly, table_index;
    sigma_j:= someSet;
    sigma_1:= [seq(i, i=1..nops(someSet))];
    non_fixed_points:= map(x -> if sigma_j[x]=x then NULL; else x; end if, [seq(i, i=1..nops(someSet))]); 
    permVect:= [seq( [  z||(sigma_1[k]) = z||(sigma_j[k]), phi||(sigma_1[k]) = phi||(sigma_j[k]), theta||(sigma_1[k]) = theta||(sigma_j[k])  ], k in non_fixed_points )]; 
    permVect:= Flatten(permVect);
    KsigmaPoly:= subs(permVect, poly); 
    return KsigmaPoly; 
end proc:
Kw:= proc(poly, forceVars:=0) 
    # alias K_omega
	#Somme sur toutes les permutations de S_N
#Ajout pour obtenir l<action diagonale seulement
    local NbVars, Vars, N, KwPoly, permutations;
	Vars:= giveVars(poly);
	#print(Vars); 
	#print(poly); 
	NbVars:= max(nops(Vars[1]), nops(Vars[2]), nops(Vars[3])); #Number of variables, (particles in CMS)
	if forceVars <> 0 then N:= forceVars; else N:=NbVars; end if; 
	if N < NbVars then print(`Error, not enough variables`); N:= NbVars; end if;
	permutations:= permute(N);	
    	#ici
	KwPoly:= map(onePerm->sort(expand(Ksigma_j(poly, onePerm))), permutations);
	#keeping only distinct permutations
	#KwPoly:= map(sort,KwPoly);
	KwPoly:= MakeUnique(KwPoly);
	KwPoly:= add(k, k in KwPoly);
	return KwPoly;
end proc:
kappa_ij:= proc(poly, i,j)
	local kappaij; 
	kappaij:= sort(subs({phi||i = phi||j, phi||j=phi||i, theta||i=theta||j, theta||j=theta||i}, poly)); 
	return kappaij; 
end proc:
MakeSubListFromList:= proc( identity_list, permutation_list)
	return [ seq( z||(identity_list[k]) = z||(permutation_list[k]), k=1..nops(identity_list))];
end proc:
AntiSymetrize:= proc(poly, variables_indices::list)
	local Apoly, perms_of_poly, subs_list, omega_sign, omega_perm, identity_perm, nbVars;
	if nops(variables_indices) < 2 then return poly; end if;
	nbVars:= nops(variables_indices);
	identity_perm:= variables_indices;
	omega_perm:= permute(variables_indices);
	omega_sign:= map(x-> sign_of_permutation(x), omega_perm);
	subs_list := map(x-> MakeSubListFromList(identity_perm, x), omega_perm);
	perms_of_poly:= map(x-> subs(x, poly), subs_list);
	Apoly:= add( omega_sign[k]*perms_of_poly[k], k=1..nops(omega_perm));
	return Apoly;
end proc:

Var_Symmetrize:= proc(poly, variables_indices::list)
	local Spoly, perms_of_poly, subs_list, omega_sign, omega_perm, identity_perm, nbVars;
	if nops(variables_indices) < 2 then return poly; end if;
	nbVars:= nops(variables_indices);
	identity_perm:= variables_indices;
	omega_perm:= permute(variables_indices);
	subs_list := map(x-> MakeSubListFromList(identity_perm, x), omega_perm);
	perms_of_poly:= map(x-> subs(x, poly), subs_list);
	Spoly:= add(perms_of_poly[k], k=1..nops(omega_perm));
	return Spoly;
end proc:
# Dunkl-Cherednik
Dunkl_i_n:= proc(i, n, poly, Nin:=0, parameter:= beta)
    local something, Vars, N, term1, term2, term3, term4, Dpoly, beta;
    option remember;
	#The Dunkl-like-Cherednik-... operator, still pretty clear code
	# i: the Dunkl index, n: the exponent, Nin: number of variables, parameter : beta, 1/alpha ... 
	if n = 0 then return poly; end if; 
	if n < 0 then return 0; end if; 
	Vars:= giveVars(poly);
	N:= max(nops(Vars[1]), nops(Vars[2]), nops(Vars[3])); #Number of variables, (particles in CMS)
    	if Nin > N then N:= Nin; end if;
	if parameter <> beta then beta := parameter end if;
	term1:= z||i * diff(poly, z||i);
	term2:= beta*add(z||i/(z||i - z||j)*(poly- Kzij(poly,i,j)), j in seq(k, k=(i-1)..1, -1));
	term3:= beta*add(z||j/(z||i - z||j)*(poly- Kzij(poly,i,j)), j in seq(k, k=(i+1)..N, 1));
	term4:= -1*beta*(i-1)*poly;
	Dpoly:= factor(term1 + term2+ term3 + term4);

	if n=1 then return Dpoly; end if;
	if n>1 then return Dunkl_i_n(i,n-1, expand(sort(Dpoly)), Nin, beta); end if;
end proc:

sign_of_permutation:= proc(L::list)
	local n, N, i, j;
	
	n:=nops(L);
	if nops(convert(L,set))=n then
		N:=0;
		for i to n-1 do
			for j from i+1 to n do
				if L[i]>L[j] then N:=N+1; fi;
			end do; 
		end do;
	else print(`Invalid input`); 
	end if;

	return (-1)^N;
end proc:


#Operations regarding the representation of S_N only with the generators s_i
get_list_perm_rep:= proc(sigma, N)
	return map(x->PermApply(sigma,x), [seq(k, k=1..N)]);
end proc:

inversion_number:= proc(k, a_list)
	local inversion_number, chopped_list, inversions;
	if k = nops(a_list) then return 0; end if;
	if nops(a_list) = 0 then return 0; end if;
	chopped_list:= a_list[(k+1)..-1];
	inversions:= map(x-> if x < a_list[k] then 1; else 0; end if, chopped_list);
	return add(l, l in inversions); 
end proc:

Total_inversions:= proc(a_list)
	local all_inversions;
	all_inversions:=map(x->inversion_number(x,a_list), [seq(k, k=1..(nops(a_list)-1))]);
	return add(k, k in all_inversions); 
end proc:

gen_coxeter_rep_of_SN:=proc(N)
	local all_perms, adj_rep, generators, longest_chain, N_terms, permutations, number_of_inversions, perms_with_numb_of_inv, wanted_perms, choose_from, choices, numb_of_inv, new_elements, stop_it, a_choice, serie_of_perm, effective_perm, permuted, where_is_it; remember;
	#Trivial terms [0] is the identity and is not included in the generators;
	generators:= [ seq([k], k=1..(N-1))];
	adj_rep:= [[0],op(generators)];
	#This is the chain that reverses completly [1...N], 
	#The idea is that you carry the 1 up to the end, then carry the 2 up to the 1, and so on and so forth
	#We see that this as exactly N(N-1)/2 terms, just like the maximal number of inversions. 
	longest_chain:= [ seq(seq( j, j=1..i), i=(N-1)..1,-1)]; 
	adj_rep:=[op(adj_rep), longest_chain]; 
	N_terms:= [seq(k, k=1..N)];
	permutations:= permute(N);
	number_of_inversions:= map(Total_inversions, permutations); 
	#We start the folling loop at 2 since we have the identity and the generators which have 
	#total number of inversion of 0 and 1
	#We also skip the last length in the number of inversion since we have longest_chain
	for numb_of_inv from 2 to (N*(N-1)/2-1) do
		perms_with_numb_of_inv := ListTools:-SearchAll(numb_of_inv, number_of_inversions);
		wanted_perms := map(x-> op(x,permutations), [perms_with_numb_of_inv]);
		choose_from:= [ seq( op(generators), k=1..ceil(numb_of_inv/2)) ];	
		choices:= permute(choose_from, numb_of_inv); 
		choices:= map(void_redundant_list, choices); 
		new_elements:=[];
		stop_it:= nops(wanted_perms); 
		for a_choice in choices do
			serie_of_perm:= list_of_index_to_perm(a_choice);
			effective_perm:= prod_of_perm(serie_of_perm);
			permuted:= get_list_perm_rep(effective_perm, N); 
			where_is_it:=ListTools:-Search(permuted, wanted_perms);
			if where_is_it <> 0 then 
				new_elements:= [op(new_elements), a_choice];
				wanted_perms:= subsop(where_is_it=NULL, wanted_perms);
			end if;
			if nops(new_ele) = stop_it then break; end if; 
		end do:
		adj_rep:=[op(adj_rep), op(new_elements)];
	end do:
		adj_rep:= map(x-> Flatten(x), adj_rep); 
	return adj_rep;
end proc:

restricted_coxeter_rep:= proc(n1,n2,N)
	local SNrep, unallowed, valid_terms;
	SNrep:= gen_coxeter_rep_of_SN(N); 
	#We remove the identity
	#SNrep:= SNrep[2..-1];
	unallowed:= { seq(k, k=1..(n1-1)), seq(k, k=(n2)..N)};
	valid_terms:=map(x-> if {op(x)} intersect unallowed = {} then x; else NULL; end if, SNrep);
	return valid_terms;
end proc:

SNcheckCoxeter:= proc(mbarbar, mbar, mubar, N)
	local S1, S2, S3, S4, Stot, doneS, Scheck;
	S1:= restricted_coxeter_rep(1,mbarbar,N);
	S2:= restricted_coxeter_rep(1+mbarbar,mbarbar+mbar,N);
	S3:= restricted_coxeter_rep(1+mbarbar+mbar,mbarbar+mbar+mubar,N);
	S4:= restricted_coxeter_rep(1+mbarbar+mbar+mubar,N,N);
	Stot:= {op(gen_coxeter_rep_of_SN(N))}; 
	doneS:= {op(S1), op(S2), op(S3), op(S4)};
	Scheck:= Stot minus doneS;
	Scheck:= [[0], op(Scheck)]; 
	return Scheck;
end proc:

void_redundant_list:= proc(list)
	local k;
	for k from 1 to nops(list)-1 do
		if list[k] = list[k+1] then return NULL;
		elif k+3 < nops(list) then
			if list[k..k+1] = list[k+2..k+3] then return NULL; end if;
		end if
	end do:
	return list;
end proc:

index_coxeter_gen_to_perm:= proc(a_gen)
	local the_val;
	the_val:= op(a_gen);
	return Perm([[the_val, the_val+1]]); 
end proc:

list_of_index_to_perm:= proc(a_list)
	return map(index_coxeter_gen_to_perm, a_list); 
end proc:

prod_of_perm:= proc(list_of_perm)
	local k, out;
	out:= Perm([]); 
	for k from 1 to nops(list_of_perm) do
		out:=PermProduct(out,list_of_perm[k]);
	end do:
end proc:


#Operators related to nsMacdo
#T_sigma operation
opTi:= proc(i, expr_z, N)
	local expr, out, out1, out2, out2b;
	if i = N then return 0; end if;
	if i = 0 then return expr_z; end if;
	expr:= expr_z;
	out1:= t*expr;
	out2:= ((t*z||i - z||(i+1))/(z||i-z||(i+1)));
	out2b:= Kzij(expr, i, i+1) - expr;
	out2:= out2*out2b;
	out:= out1 + out2;
#	out:= t*expr + ((t*z||i - z||(i+1))/(z||i-z||(i+1)))*(Kzij(expr,i, i+1) - expr);
	#out:= simplify(factor(out)); 
	return out;
end proc:

inv_opTi:= proc(i, expr_z, N)
	local expr, out;
	return simplify(factor((t^(-1) - 1)*expr_z + t^(-1)*opTi(i, expr_z, N))); 
end proc:

opT_sigma:= proc(sigma, expr, N) 
	local out,k;
	out:= expr; 
	for k from 1 to nops(sigma) do
		out:= factor(opTi(sigma[-k], out, N)); 
	end do:
	return out;
end proc:

tSymmetrize:= proc(expr_z, N, n1:=0, n2:=0)
	local coxeterSN, out, sigma;
	if n1 = 0 then 
		coxeterSN:= gen_coxeter_rep_of_SN(N); 	
	else
		coxeterSN:= restricted_coxeter_rep(n1,n2,N);
	end if;
	out:= 0; 
	for sigma in coxeterSN do
		out:= out + opT_sigma(sigma, expr_z,N);
	end do:
	out:= factor(out); 
	return out;
end proc:
tVandermonde:= proc(the_range, remove_t:=0)
	local N, out;
	N:= the_range[2]-the_range[1];
	out:= t^(-N*(N-1)/2)*mul(mul( t*z||i - z||j, i=the_range[1]..(j-1)), j=the_range[1]..the_range[2]); 
	if remove_t <> 0 then out:= subs(t=1, out); end if;
	return out;
end proc:
tantiSymmetrize:= proc(expr_z, n1:=0, n2:=0)
	local coxeterSN, out, sigma;
	out:= AntiSymetrize(expr_z, [seq(k,k=n1..n2)]);
	out:= tVandermonde([n1,n2])/tVandermonde([n1,n2],1)*out;
	out:= factor(out);
	return out;
end proc:
bkp_tantiSymmetrize:= proc(expr_z, N, n1:=0, n2:=0)
	local coxeterSN, out, sigma, permsign;
	if n1 = 0 then 
		coxeterSN:= gen_coxeter_rep_of_SN(N); 	
	else
		coxeterSN:= restricted_coxeter_rep(n1,n2,N);
	end if;
	out:= 0; 
	for sigma in coxeterSN do
		permsign:= nops(sigma); 
		out:= out + (-1*t)^permsign*opT_sigma(sigma, expr_z,N);
	end do:
	out:= factor(out); 
	return out;
end proc:
apply_sigma_si:= proc(expr, sigma)
	local out, k,i;
	if sigma = [0] then return expr; end if; 
	out:= expr;
	for k from 1 to nops(sigma) do
		i := sigma[-k];
		out:= Kscrypt_ij(out, [i, i+1])
	end do:
	return out; 
end proc:

var_omega:= proc(expr, N)
	local out, k;
	out:= opTaui(1,expr); 
	for k from 1 to (N-1) do
		out:= Kzij(out,k,k+1); 
	end do:
	return out;
end proc:

opTaui:= proc(i,expr)
	return factor(subs(z||i = q*z||i, expr)); 
end proc:

opYi:= proc(i, expr, N)
	local out, k;
	out:=expr;
	if i > 1 then
		for k from (i-1) to 1 by -1 do
			out:= inv_opTi(k, out, N);
		end do:
	end if;
	out:= var_omega(out, N); 
	if i <> N then
		for k from (N-1) to i by -1 do
			out:= opTi(k,out, N);
		end do:
	end if;
	out:=factor(t^(-N+i)*out); 
	return out;
end proc:

eigen_val_opYi:= proc(i, eta)
	local qexp,leta1,leta2,leta, out;
	qexp:= eta[i];
	if i >1 then 
		leta1:= map(x-> if x>= eta[i] then 1; else 0; end if, eta[1..(i-1)]);
	else
		leta1:=0; 
	end if;
	if i<nops(eta) then
		leta2:= map(x-> if x>eta[i] then 1; else 0; end if, eta[(i+1)..-1]); 
	else
		leta2:= 0;
	end if;
	leta:= add(k, k in leta1) + add(k, k in leta2); 
	out:= q^(qexp)*t^(-leta);
	return out; 
end proc:


