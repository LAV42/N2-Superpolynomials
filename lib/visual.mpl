with(StringTools):
DiagLatex := proc(spart, size:=0)
	local phis, thetas, phithetas, zeds, Lambda, string, cercle, triangle, triangle_cercle, boite, part, endline, k;
	phis:= spart[2];
	phis:= map( x-> [x,"c"], phis);
	thetas:= spart[3];
	thetas:= map(x-> [x,"b"], thetas);
	phithetas:= spart[1];
	phithetas:= map(x-> [x,"d"], phithetas);
	zeds:= spart[4];
	zeds:= map(x-> [x,"a"], zeds);
	Lambda:= sort([op(phithetas),op(phis), op(thetas), op(zeds)]);

	string:="";
	
	cercle:= "\\yC";
	triangle:= "\\yT";
	triangle_cercle:= "\\yTC"; 
	boite:= "\\,";
	for k from 1 to nops(Lambda) do
		part:= Lambda[k];
		print(Lambda);
		print(part);
		if k = 1 then endline:=""; else endline:="\\\\ \n"; end if:
		if part[2] = "c" then
			string:= cat(cat(Repeat(cat(boite, "& "), part[1]), triangle, endline), string);
		elif part[2] = "b" then
			string:= cat(cat(Repeat(cat(boite, "& "), part[1]), cercle, endline), string);
		elif part[2] = "a" then
			string:= cat(cat(Repeat(cat(boite, "& "), part[1]-1), boite, endline), string);
		elif part[2] = "d" then 
			string:= cat(cat(Repeat(cat(boite, "& "), part[1]), triangle_cercle, endline), string);
		end if;
	end do:
	if size = 0 then
		string:= cat("{\\, \\superYsmall{", string, "}}");
	elif size = 1 then
		string:= cat("{\\, \\superY{", string, "}}");
	elif size = 2 then
		string:= cat("\\superRusse{{\\superY{", string, "}}}");
	end if;
	return string;
end proc:

superLatex := proc(expr,initial_term:=0, wipe:=0)
	local sparts, astring, spart, spart_string, fd, basetype, terms, thecoeff, latexsparts, latex_terms, k, ou;
	if wipe <> 0 then 
		fd:= fopen("out.txt", WRITE);
		fprintf(fd, "");
		fclose(fd);
	else
		fd:=fopen("out.txt", APPEND);
		fprintf(fd,"new \n \\begin{gather*} \n");
		fclose(fd);
	end if;
	basetype:= "m";
	terms:= [op(indets(expr, 'superindexed'))];
	terms:= sort(terms, list_sort); 
	#print(terms);
	sparts:= map(x-> [op(x)], terms); 
	#print(sparts);
	thecoeff:= map(x-> coeff(expr, x), terms);
	#print(thecoeff); 
	#latexcoeff:= map(x-> latex(x), thecoeff); 

	#Activate following line for diagrams
	#latexsparts:= map(x-> DiagLatex(x,0), sparts);
	#Activate following line for sparts
	latexsparts:= map(x-> SpartLatex(x),sparts);
	latex_terms:= [];
	if initial_term <> 0 then
		fd:=fopen("out.txt", APPEND);
		fprintf(fd,cat(initial_term[1],"\\,",basetype,"_",DiagLatex(initial_term[2], 0),"=","\n+"));
		fclose(fd);
	end if;
	for k from 1 to nops(sparts) do
		fd:= fopen("out.txt", APPEND);
		fprintf(fd, "\t");
		fclose(fd);
		if whattype(thecoeff[k]) = `+` then 
			fd:= fopen("out.txt", APPEND);
			fprintf(fd, "(");
			fclose(fd);
		end if;

		latex(thecoeff[k],"out.txt",'append'); 

		if whattype(thecoeff[k]) = `+` then 
			fd:= fopen("out.txt", APPEND);
			fprintf(fd, ")");
			fclose(fd);
		end if;
		fd:= fopen("out.txt", APPEND);
		fprintf(fd, cat(basetype,"_",latexsparts[k],"\n+"));
		fclose(fd);
	end do:
		fd:=fopen("out.txt", APPEND);
		fprintf(fd,"\\end{gather*} \n");
		fclose(fd);
end proc:

SpartLatex:= proc(spart)
	local pts, phis, thetas, zeds, pt_string, phi_string, theta_string, zed_string, SpartString;
	pts:= spart[1];
	phis:= spart[2];
	thetas:= spart[3];
	zeds:= spart[4];

	pt_string:= convert(pts, string);
	phi_string:= convert(phis, string);
	theta_string:= convert(thetas, string);
	zed_string:= convert(zeds, string);

	pt_string:= Substitute(pt_string, "[", "(");
	pt_string:= Substitute(pt_string, "]", ";\\,");
	phi_string:= Substitute(phi_string, "[", "");
	phi_string:= Substitute(phi_string, "]", ";\\,");
	theta_string:= Substitute(theta_string, "[", "");
	theta_string:= Substitute(theta_string, "]", ";\\,");
	zed_string:= Substitute(zed_string, "[", "");
	zed_string:= Substitute(zed_string, "]", ")");

	SpartString:= cat(pt_string, phi_string, theta_string, zed_string); 
	SpartString:= cat("{",SpartString, "}");
	return SpartString;
end proc:
