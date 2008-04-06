indexing
	description: "A fuel pod."

class
	FUEL_POD

inherit
	NEUTRAL_ENTITY
	FUELABLE
	STATIC_ENTITY

feature -- Queries

feature -- Commands

invariant -- Constraints
	-- A fuel pod is destroyed by a bullet.
	-- The fuel pod is not affected by the goal sphere.
	-- The fuel pod is not affected by the spaceship.
	-- A fuel pod's outline color is always yellow.
	-- A fuel pod's "fuel" lettering color is dictated by the amount of fuel it contains.

end
