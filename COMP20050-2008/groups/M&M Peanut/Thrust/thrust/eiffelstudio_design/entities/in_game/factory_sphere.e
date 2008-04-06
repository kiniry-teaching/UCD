indexing
	description: "A sphere of a factory."

class
	FACTORY_SPHERE

inherit
	NEUTRAL_ENTITY
	STATIC_ENTITY

feature -- Queries

feature -- Commands

invariant -- Constraints
	-- A factory sphere's color is always green.
	-- The goal sphere is not destroyed by a factory's sphere.

end
