// Generated with util/create-component.js
import React, { useCallback, useRef } from "react";
import Button from "@mui/material/Button";
import MenuItem from "@mui/material/MenuItem";
import Menu from "@mui/material/Menu";
import Linked from "components/Linked/Linked";
import { DropdownMenuItemProps } from "./DropdownMenuItem.types";
import Grid from "@mui/material/Grid";
import Typography from "@mui/material/Typography";
import Box from "@mui/material/Box";
import MegaMenuContent from "components/MegaMenuContent/MegaMenuContent";
import { Fade, Slide, Grow, Zoom } from "@mui/material";
/**
 *
 * @param {DropdownMenuItemProps} object props
 * @returns {React.Component} DropdownMenuItem
 */
const DropdownMenuItem: React.FC<DropdownMenuItemProps> = ({
  menuItem,
  menuShowingDropdown,
  setMenuShowingDropdown,
}) => {
  const { title, subMenus = null, megaMenuContent = null } = menuItem;
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
  const CustomSlide = <Slide direction="up" />;
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
          showSubMenu();
        }}
        onMouseLeave={() => {
          setMenuShowingDropdown("");
        }}
        onMouseEnter={() => {
          showSubMenu();
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
          elevation: 1,
          sx: {
            border: (theme) => `1px solid ${theme.palette.text.primary}`,
          },
        }}
        sx={{
          marginTop: 1,
        }}
        TransitionComponent={Fade}
        anchorEl={buttonRef.current}
        open={menuShowingDropdown === menuItem.title}
        onClose={closeSubMenu}
      >
        <>
          {megaMenuContent && <MegaMenuContent content={megaMenuContent!} />}
          {subMenus && subMenusNodes}
        </>
      </Menu>
    </>
  );
};

export default DropdownMenuItem;
