a=10
b=1
d = 4
case a 
	when c = 10 then a=1; b=nil
	when d then a=2; c=2
	else a=3
end
a.to_s		#NonNil (definito in tutti i casi)
b.to_s		#MaybeNil
c.to_s		#MaybeNil (definito solo in un ramo)
