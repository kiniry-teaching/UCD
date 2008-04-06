indexing
	description: "An enemy gun turrent that shoots bullets at the spaceship."

class
	GUN_TURRENT

inherit
	ENEMY_ENTITY
	STATIC_ENTITY

feature -- Queries

feature -- Commands

invariant -- Constraints
	-- A gun turrent always resides on/adjacent to the terrain.
	-- A gun turrent's color is always green.

end
