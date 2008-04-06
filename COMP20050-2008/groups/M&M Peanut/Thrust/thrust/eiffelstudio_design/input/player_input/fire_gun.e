indexing
	description: "Fire a bullet from the spaceship's gun."

class
	FIRE_GUN

inherit
	KEYBOARD_INPUT

feature -- Queries
	keycode: CHARACTER is
		once
			Result := '%N'
		end

feature -- Commands

invariant -- Constraints
	-- The keycode for looking at the high score list is always '\n' (the return key).
	keycode_is_newline: keycode = '%N'

end
