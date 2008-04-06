indexing
	description: "All of the sound effects that are heard in the game."

class
	SOUND_EFFECTS

feature -- Queries

	-- What are all of the game's sound effects?
	effects: LINKED_LIST[SOUND_EFFECT]

	-- What is the sound effect for firing the gun?
	-- What is the sound effect for using the engine?
	-- What is the sound effect for using the shield?

feature -- Commands
	-- The sound effect for firing the gun is 'e'.
	-- The sound effect for using the engine is 'e'.
	-- The sound effect for using the shield is 'e'.

invariant -- Constraints

end
