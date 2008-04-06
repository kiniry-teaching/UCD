indexing
	description: "Use the spaceship's engine to apply thrust forward."

class
	USE_ENGINE

inherit
	KEYBOARD_INPUT

feature -- Queries
	keycode: CHARACTER is
		once
			Result := ' '
		end

feature -- Commands

invariant -- Constraints
	-- The keycode for using the engine is always the shift key.
	keycode_is_shift: keycode = ' '

end
