a=4
b=2
c = 2
d = 4
case b 
	when c then b=3
	when d then a.to_s
	else a=3; b = 9; c=10
end
#a.to_s		#NonNil (definito in tutti i casi)
#b.to_s		#MaybeNil
#c.to_s		#MaybeNil (definito solo in un ramo)
