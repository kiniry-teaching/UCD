indexing
	description: "An entity that can contain fuel."

class
	FUELABLE

feature -- Queries
	-- How much fuel do you contain?
	-- How much mass does your fuel have?

feature -- Commands
	-- You have 'f' units of fuel.

invariant -- Constraints
	-- An entity may only have non-negative units of fuel.

end
