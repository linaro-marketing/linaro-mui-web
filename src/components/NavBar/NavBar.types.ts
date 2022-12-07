import { AppBarProps } from "@mui/material";
// Generated with util/create-component.js
export interface NavBarProps extends AppBarProps {
  /**
   * The link that the logo will point to.
   */
  logoLink: string;
  /**
   * The site title fallback if no logo is provided.
   */
  title?: string;
  /**
   * The logo to be displayed in the NavBar.
   */
  logo?: string;
  /**
   * The pages to be displayed in the NavBar.
   */
  pages: {
    title: string;
    link: string;
  }[];
}
