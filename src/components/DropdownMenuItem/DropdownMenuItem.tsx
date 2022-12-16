// Generated with util/create-component.js
import React, { useCallback, useRef } from "react";
import Button from "@mui/material/Button";
import MenuItem from "@mui/material/MenuItem";
import Menu from "@mui/material/Menu";
import Linked from "components/Linked/Linked";
import { DropdownMenuItemProps } from "./DropdownMenuItem.types";
const DropdownMenuItem: React.FC<DropdownMenuItemProps> = ({
  menuItem,
  menuShowingDropdown,
  setMenuShowingDropdown,
}) => {
  const { title, subMenus } = menuItem;
  const buttonRef = useRef<null | HTMLButtonElement>(null);

  const showSubMenu = useCallback(() => {
    setMenuShowingDropdown(menuItem.title);
  }, [menuItem.title, setMenuShowingDropdown]);

  const closeSubMenu = useCallback(() => {
    setMenuShowingDropdown("");
  }, [setMenuShowingDropdown]);

  const subMenusNodes = subMenus?.map((subMenuItem, index) => {
    return (
      <Linked to={subMenuItem.pathname} key={index}>
        <MenuItem key={index} component="div">
          {subMenuItem.title}
        </MenuItem>
      </Linked>
    );
  });
  return (
    <>
      <Button
        id={`menuItem-${title}`}
        // higher zIndex to make button show submenu when move mouse from another submenu
        ref={buttonRef}
        sx={{
          textTransform: "none",
          fontSize: "1rem",
          zIndex: (theme) => theme.zIndex.modal + 1,
        }}
        color="inherit"
        onClick={() => {
          if (!menuItem.subMenus) {
            console.log("first level menu click");
          }
        }}
        onMouseLeave={() => {
          setMenuShowingDropdown("");
        }}
        onMouseEnter={() => {
          if (menuItem.subMenus) {
            showSubMenu();
          }
        }}
      >
        {title}
      </Button>
      <Menu
        PaperProps={{
          onMouseEnter: () => {
            showSubMenu();
          },
          onMouseLeave: () => {
            closeSubMenu();
          },
        }}
        sx={{
          marginTop: 1,
        }}
        anchorEl={buttonRef.current}
        open={menuShowingDropdown === menuItem.title}
        onClose={closeSubMenu}
      >
        {subMenusNodes}
      </Menu>
    </>
  );
};

export default DropdownMenuItem;
