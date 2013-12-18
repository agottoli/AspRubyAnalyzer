a=nil
b=1
case a 
	when 1 then a=1; b=nil
	when 2 then a=2; c=2
	else a=3
end
a.to_s		#NonNil (definito in tutti i casi)
b.to_s		#MaybeNil
c.to_s		#MaybeNil (definito solo in un ramo)
