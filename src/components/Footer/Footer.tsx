// Generated with util/create-component.js
import React from "react";
import Box from "@mui/material/Box";
import Grid from "@mui/material/Grid";
import List from "@mui/material/List";
import ListItemText from "@mui/material/ListItemText";
import ListSubheader from "@mui/material/ListSubheader";
import Container from "@mui/material/Container";
import Divider from "@mui/material/Divider";
import ListItem from "@mui/material/ListItem";
import IconButton from "@mui/material/IconButton";
import Linked from "components/Linked/Linked";
import { FooterCol, FooterLink, FooterProps } from "./Footer.types";
import { dashboardLinksIconMapper } from "lib/icons";

const FooterColumn: React.FC<{ column: FooterCol; colIndex: number }> = ({
  column,
  colIndex,
}) => {
  let extraProps = {};
  if (column?.title) {
    extraProps = {
      "aria-labelledby": `footer-list-subheader-${colIndex}`,
      subheader: (
        <ListSubheader component="div" id={`footer-list-subheader-${colIndex}`}>
          {column.title}
        </ListSubheader>
      ),
    };
  }
  return (
    <List {...extraProps}>
      {column.links.map((link: FooterLink, index: number) => {
        return (
          <ListItem key={index}>
            <Linked to={link.pathname} textLink>
              <ListItemText primary={link.title} />
            </Linked>
          </ListItem>
        );
      })}
    </List>
  );
};

const SocialIcons: React.FC<{ icons: SocialIcons }> = ({ icons }) => {
  return (
    <Box>
      {icons.map((icon, index) => {
        const Icon = dashboardLinksIconMapper[icon];
        return (
          <IconButton>
            <Icon />
          </IconButton>
        );
      })}
    </Box>
  );
};
const Footer: React.FC<FooterProps> = ({ columns }) => {
  return (
    <Box
      component="footer"
      sx={{
        backgroundColor: "background.default",
      }}
    >
      <Container maxWidth="xl">
        <Grid container>
          {columns.map((column, index) => {
            return (
              <Grid item xs={12} md={4} key={index}>
                <FooterColumn column={column} colIndex={index} />
              </Grid>
            );
          })}
          <Grid item xs={12}>
            <Divider />
          </Grid>
        </Grid>
      </Container>
    </Box>
  );
};
export default Footer;
