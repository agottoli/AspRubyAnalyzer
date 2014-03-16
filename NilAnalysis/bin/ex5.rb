a=4
b=2
c = 2
d = 4
case b 
	when c then 
		b = 3; 
		a = a + 1; 
		c = d - b
	when d then 
		a.to_s
	else 
		a = 3; 
		b = 9; 
		c = 10
end
a.to_s		
b.to_s		
c.to_s
	
