indexing
	description: "The force that an object has due to its velocity and mass."
	definition: "http://en.wikipedia.org/wiki/Momentum"

class
	MOMENTUM

feature -- Queries
	-- What is your momentum?

feature -- Commands

invariant -- Constraints
	-- Momentum is measured in kilogram times meters per second (kg m/s).
	-- Momentum is the product of mass and velocity.
	-- Momentum is a conserved quantity in a closed physics system.

end
