// Generated with util/create-component.js
import React, { useState, useCallback, useRef } from "react";
import AppBar from "@mui/material/AppBar";
import Box from "@mui/material/Box";
import Toolbar from "@mui/material/Toolbar";
import IconButton from "@mui/material/IconButton";
import Typography from "@mui/material/Typography";
import MenuIcon from "@mui/icons-material/Menu";
import CloseIcon from "@mui/icons-material/Close";
import Container from "@mui/material/Container";
import Button from "@mui/material/Button";
import { NavBarProps } from "./NavBar.types";
import Linked from "components/Linked/Linked";
import DropdownMenuItem from "components/DropdownMenuItem/DropdownMenuItem";
import DrawerLinks from "components/DrawerLinks/DrawerLinks";
import Drawer from "@mui/material/Drawer";
import DarkModeToggle from "components/DarkModeToggle/DarkModeToggle";

const NavBarLogo = ({ logo, title }: { logo?: string; title: string }) => {
  return (
    <>
      {logo && (
        <Box
          sx={{
            display: "flex",
            alignItems: "center",
            justifyContent: "center",
            width: "100px",
            mr: 2,
            "& img": {
              width: "100px",
              height: "50px",
              objectFit: "contain",
            },
          }}
        >
          <img src={logo} alt="logo" />
        </Box>
      )}
      {!logo && (
        <Typography
          variant="h6"
          noWrap
          component="a"
          href="/"
          sx={{
            mr: 2,
            display: { xs: "none", md: "flex" },
            fontFamily: "monospace",
            fontWeight: 700,
            letterSpacing: ".3rem",
            color: "inherit",
            textDecoration: "none",
          }}
        >
          {title}
        </Typography>
      )}
    </>
  );
};

const NavBar: React.FunctionComponent<NavBarProps> = ({
  pages,
  logoLink,
  logo,
  toggleTheme,
  themeMode = null,
  title = "Linaro",
  ...rest
}) => {
  const [drawerOpen, setDrawerOpen] = React.useState<boolean>(false);

  const [menuShowingDropdown, setMenuShowingDropdown] = useState("");
  const handleMenuShowingDropdownChange = useCallback((menuTitle: string) => {
    setMenuShowingDropdown(menuTitle);
  }, []);

  const handleOpenNavMenu = (event: React.MouseEvent<HTMLElement>) => {
    setDrawerOpen(true);
  };
  const handleCloseNavMenu = () => {
    setDrawerOpen(false);
  };

  return (
    <>
      <AppBar color="default" elevation={1} position="static" {...rest}>
        <Container maxWidth="xl">
          <Toolbar
            disableGutters
            sx={{
              width: "100%",
              display: "flex",
              justifyContent: "space-between",
              alignItems: "center",
            }}
          >
            <Box>
              <Linked to={logoLink}>
                <NavBarLogo logo={logo} title={title} />
              </Linked>
            </Box>
            <Box
              sx={{
                flexGrow: 1,
                display: { xs: "flex", md: "none" },
                justifyContent: "flex-end",
                alignItems: "center",
              }}
            >
              <IconButton
                size="large"
                aria-label="account of current user"
                aria-controls="menu-appbar"
                aria-haspopup="true"
                onClick={handleOpenNavMenu}
                color="inherit"
              >
                <MenuIcon />
              </IconButton>
            </Box>
            <Box
              sx={{
                flexGrow: 1,
                justifyContent: "flex-end",
                alignItems: "center",
                display: { xs: "none", md: "flex" },
              }}
            >
              {pages.map((page, index) => {
                if (page?.pathname) {
                  return (
                    <Linked to={page.pathname} key={index}>
                      <Button
                        key={index}
                        sx={{
                          textTransform: "none",
                          fontSize: "1rem",
                        }}
                        color="inherit"
                        component="span"
                        onClick={handleCloseNavMenu}
                      >
                        {page.title}
                      </Button>
                    </Linked>
                  );
                } else if (page?.subMenus || page?.megaMenuContent) {
                  return (
                    <DropdownMenuItem
                      menuItem={page}
                      menuShowingDropdown={menuShowingDropdown}
                      setMenuShowingDropdown={handleMenuShowingDropdownChange}
                    />
                  );
                } else {
                  return (
                    <Button
                      key={index}
                      sx={{
                        textTransform: "none",
                        fontSize: "1rem",
                      }}
                      color="inherit"
                      component="span"
                      onClick={handleCloseNavMenu}
                    >
                      {page.title}
                    </Button>
                  );
                }
              })}
              {themeMode && (
                <DarkModeToggle
                  variant="icon"
                  toggleTheme={toggleTheme!}
                  themeMode={themeMode}
                />
              )}
            </Box>
          </Toolbar>
        </Container>
      </AppBar>
      <Drawer
        variant="temporary"
        anchor={"left"}
        open={drawerOpen}
        onClose={handleCloseNavMenu}
        sx={{
          "& 	.MuiDrawer-paper": {
            width: "100%",
          },
          display: { xs: "block", md: "none" },
        }}
        ModalProps={{
          keepMounted: true, // Better open performance on mobile.
        }}
      >
        <AppBar color="inherit" elevation={1} position="static" {...rest}>
          <Container maxWidth="xl">
            <Toolbar
              disableGutters
              sx={{
                width: "100%",
                display: "flex",
                justifyContent: "space-between",
                alignItems: "center",
              }}
            >
              <Box
                sx={{
                  flexGrow: 1,
                  display: { xs: "flex", md: "none" },
                  justifyContent: "flex-end",
                  alignItems: "flex-start",
                }}
              >
                <IconButton
                  size="large"
                  aria-label="close drawer"
                  onClick={handleCloseNavMenu}
                  color="inherit"
                >
                  <CloseIcon />
                </IconButton>
              </Box>
            </Toolbar>
          </Container>
        </AppBar>
        <DrawerLinks pages={pages} />
      </Drawer>
    </>
  );
};
export default NavBar;
