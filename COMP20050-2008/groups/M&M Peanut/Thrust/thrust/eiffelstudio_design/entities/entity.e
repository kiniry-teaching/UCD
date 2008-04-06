indexing
	description: "Any entity in the game that is drawn in space or on the terrain."

deferred class
	ENTITY

feature -- Queries
	-- What is your shape?
	shape: SHAPE
	-- What is your color?
	color: COLOR

feature -- Commands
	-- Render yourself.
	-- Your color is 'c'.
	-- Your shape is 's'.

invariant -- Constraints
	-- All entities have a color.
	-- All entities have a shape.

end
